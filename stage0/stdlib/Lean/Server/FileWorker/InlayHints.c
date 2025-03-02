// Lean compiler output
// Module: Lean.Server.FileWorker.InlayHints
// Imports: Lean.Server.GoTo Lean.Server.Requests
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5;
lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instInhabitedInlayHintState;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_documentUriFromModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__2;
static lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__4;
lean_object* l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3;
lean_object* l_EStateM_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__2;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toLspInlayHintKind___boxed(lean_object*);
static lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_Mutex_new___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonInlayHint____x40_Lean_Data_Lsp_LanguageFeatures___hyg_12835_(lean_object*);
static lean_object* l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__1;
static lean_object* l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104_(lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__3;
extern lean_object* l_Lean_Server_requestHandlers;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__4(lean_object*);
static lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__3;
lean_object* l_EStateM_instMonad(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_PersistentArray_toList___rarg(lean_object*);
static size_t l_Lean_Server_FileWorker_handleInlayHints___closed__6;
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__1;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__4___boxed(lean_object*);
lean_object* l_Lean_initializing(lean_object*);
lean_object* l_Lean_Server_RequestContext_srcSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(lean_object*, lean_object*);
static lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError;
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__1;
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2;
uint8_t l_String_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__4;
lean_object* l_Lean_Server_RequestM_mapTaskCostly___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__3(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__5;
lean_object* l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__1(lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InlayHint_resolveDeferred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4(lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(size_t, size_t, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__1;
static lean_object* l_Lean_Server_FileWorker_InlayHintState_init___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintTextEdit_toLspTextEdit___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintInfo_toLspInlayHint___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instTypeNameInlayHintState;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__3;
lean_object* l_StateT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__1;
lean_object* l_String_Range_bsize(lean_object*);
uint8_t l_String_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InlayHintKind_toLspInlayHintKind(uint8_t);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_InlayHintState_init;
lean_object* l_Lean_Server_RequestCancellationToken_cancellationTask(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
static lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__1;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintInfo_toLspInlayHint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__3;
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonInlayHintParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_11544_(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__7;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__1;
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Server_documentUriFromModule(x_1, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = l_Lean_FileMap_utf8RangeToLspRange(x_2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_7, 0, x_20);
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_3, 1);
x_23 = l_Lean_FileMap_utf8RangeToLspRange(x_2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_28 = x_7;
} else {
 lean_dec_ref(x_7);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_3, 1);
x_30 = l_Lean_FileMap_utf8RangeToLspRange(x_2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_27; 
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
x_5 = x_28;
x_6 = x_4;
goto block_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(x_1, x_2, x_29, x_4);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_5 = x_31;
x_6 = x_32;
goto block_26;
}
else
{
uint8_t x_33; 
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
block_26:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_8, 0, x_16);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_5);
lean_ctor_set(x_17, 3, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(x_1, x_2, x_9, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_array_size(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___spec__1(x_1, x_2, x_12, x_13, x_11, x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_3, 0, x_16);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_3);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_array_size(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___spec__1(x_1, x_2, x_25, x_26, x_24, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InlayHintKind_toLspInlayHintKind(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toLspInlayHintKind___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_FileMap_utf8RangeToLspRange(x_1, x_3);
x_6 = lean_box(0);
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintTextEdit_toLspTextEdit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintInfo_toLspInlayHint___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(x_1, x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_2);
x_6 = l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(x_1, x_2, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_inc(x_2);
x_10 = l_Lean_FileMap_utf8PosToLspPos(x_2, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 3);
lean_inc(x_12);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintInfo_toLspInlayHint___spec__1(x_2, x_13, x_14, x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_ctor_get(x_3, 4);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 1);
lean_dec(x_3);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_20);
lean_ctor_set(x_25, 6, x_23);
lean_ctor_set(x_25, 7, x_24);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = 1;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_17, 0, x_30);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_8);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_16);
lean_ctor_set(x_31, 4, x_17);
lean_ctor_set(x_31, 5, x_20);
lean_ctor_set(x_31, 6, x_23);
lean_ctor_set(x_31, 7, x_24);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_8);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_16);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_20);
lean_ctor_set(x_37, 6, x_23);
lean_ctor_set(x_37, 7, x_24);
lean_ctor_set(x_6, 0, x_37);
return x_6;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
x_41 = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(x_40);
x_42 = lean_box(x_41);
lean_ctor_set(x_11, 0, x_42);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_8);
lean_ctor_set(x_43, 2, x_11);
lean_ctor_set(x_43, 3, x_16);
lean_ctor_set(x_43, 4, x_24);
lean_ctor_set(x_43, 5, x_20);
lean_ctor_set(x_43, 6, x_23);
lean_ctor_set(x_43, 7, x_24);
lean_ctor_set(x_6, 0, x_43);
return x_6;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = 1;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_17, 0, x_48);
x_49 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_49, 0, x_10);
lean_ctor_set(x_49, 1, x_8);
lean_ctor_set(x_49, 2, x_11);
lean_ctor_set(x_49, 3, x_16);
lean_ctor_set(x_49, 4, x_17);
lean_ctor_set(x_49, 5, x_20);
lean_ctor_set(x_49, 6, x_23);
lean_ctor_set(x_49, 7, x_24);
lean_ctor_set(x_6, 0, x_49);
return x_6;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_17, 0);
lean_inc(x_50);
lean_dec(x_17);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_8);
lean_ctor_set(x_55, 2, x_11);
lean_ctor_set(x_55, 3, x_16);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_20);
lean_ctor_set(x_55, 6, x_23);
lean_ctor_set(x_55, 7, x_24);
lean_ctor_set(x_6, 0, x_55);
return x_6;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
x_58 = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(x_57);
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_10);
lean_ctor_set(x_61, 1, x_8);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_16);
lean_ctor_set(x_61, 4, x_24);
lean_ctor_set(x_61, 5, x_20);
lean_ctor_set(x_61, 6, x_23);
lean_ctor_set(x_61, 7, x_24);
lean_ctor_set(x_6, 0, x_61);
return x_6;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_17, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_63 = x_17;
} else {
 lean_dec_ref(x_17);
 x_63 = lean_box(0);
}
x_64 = 1;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_10);
lean_ctor_set(x_68, 1, x_8);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_16);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_20);
lean_ctor_set(x_68, 6, x_23);
lean_ctor_set(x_68, 7, x_24);
lean_ctor_set(x_6, 0, x_68);
return x_6;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_69 = lean_ctor_get(x_6, 0);
x_70 = lean_ctor_get(x_6, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_6);
x_71 = lean_ctor_get(x_3, 0);
lean_inc(x_71);
lean_inc(x_2);
x_72 = l_Lean_FileMap_utf8PosToLspPos(x_2, x_71);
lean_dec(x_71);
x_73 = lean_ctor_get(x_3, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 3);
lean_inc(x_74);
x_75 = lean_array_size(x_74);
x_76 = 0;
x_77 = l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintInfo_toLspInlayHint___spec__1(x_2, x_75, x_76, x_74);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_ctor_get(x_3, 4);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 1);
lean_dec(x_3);
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_box(0);
if (lean_obj_tag(x_73) == 0)
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_69);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_78);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_87, 5, x_82);
lean_ctor_set(x_87, 6, x_85);
lean_ctor_set(x_87, 7, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_70);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_90 = x_79;
} else {
 lean_dec_ref(x_79);
 x_90 = lean_box(0);
}
x_91 = 1;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_90;
}
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_95, 0, x_72);
lean_ctor_set(x_95, 1, x_69);
lean_ctor_set(x_95, 2, x_86);
lean_ctor_set(x_95, 3, x_78);
lean_ctor_set(x_95, 4, x_94);
lean_ctor_set(x_95, 5, x_82);
lean_ctor_set(x_95, 6, x_85);
lean_ctor_set(x_95, 7, x_86);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_70);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_73, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_98 = x_73;
} else {
 lean_dec_ref(x_73);
 x_98 = lean_box(0);
}
x_99 = lean_unbox(x_97);
lean_dec(x_97);
x_100 = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(x_99);
x_101 = lean_box(x_100);
if (lean_is_scalar(x_98)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_98;
}
lean_ctor_set(x_102, 0, x_101);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_103, 0, x_72);
lean_ctor_set(x_103, 1, x_69);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_78);
lean_ctor_set(x_103, 4, x_86);
lean_ctor_set(x_103, 5, x_82);
lean_ctor_set(x_103, 6, x_85);
lean_ctor_set(x_103, 7, x_86);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_70);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_105 = lean_ctor_get(x_79, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_106 = x_79;
} else {
 lean_dec_ref(x_79);
 x_106 = lean_box(0);
}
x_107 = 1;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
if (lean_is_scalar(x_106)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_106;
}
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_111, 0, x_72);
lean_ctor_set(x_111, 1, x_69);
lean_ctor_set(x_111, 2, x_102);
lean_ctor_set(x_111, 3, x_78);
lean_ctor_set(x_111, 4, x_110);
lean_ctor_set(x_111, 5, x_82);
lean_ctor_set(x_111, 6, x_85);
lean_ctor_set(x_111, 7, x_86);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_70);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_6);
if (x_113 == 0)
{
return x_6;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_6, 0);
x_115 = lean_ctor_get(x_6, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_6);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintInfo_toLspInlayHint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_InlayHintInfo_toLspInlayHint___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Got position ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" that should have been invalidated by edit at range ", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.FileWorker.InlayHints", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.FileWorker.applyEditToHint\?", 39, 39);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_6, x_5, x_9);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_13 = x_8;
} else {
 lean_dec_ref(x_8);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_16 = x_11;
} else {
 lean_dec_ref(x_11);
 x_16 = lean_box(0);
}
x_17 = lean_nat_dec_lt(x_3, x_14);
x_18 = lean_nat_dec_lt(x_3, x_15);
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
if (x_17 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_nat_dec_lt(x_14, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_54 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_55 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_52);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
x_61 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3;
x_62 = lean_string_append(x_60, x_61);
lean_inc(x_3);
x_63 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_64 = lean_string_append(x_62, x_63);
lean_dec(x_63);
x_65 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
x_66 = lean_string_append(x_64, x_65);
x_67 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5;
x_68 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6;
x_69 = lean_unsigned_to_nat(83u);
x_70 = lean_unsigned_to_nat(6u);
x_71 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_67, x_68, x_69, x_70, x_66);
lean_dec(x_66);
x_72 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_71);
if (x_18 == 0)
{
x_21 = x_72;
goto block_51;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_16);
lean_dec(x_13);
x_73 = lean_nat_to_int(x_15);
x_74 = lean_int_add(x_73, x_2);
lean_dec(x_73);
x_75 = l_Int_toNat(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_12);
x_78 = lean_array_uset(x_10, x_5, x_77);
x_5 = x_20;
x_6 = x_78;
goto _start;
}
}
else
{
lean_dec(x_52);
if (x_18 == 0)
{
x_21 = x_14;
goto block_51;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_16);
lean_dec(x_13);
x_80 = lean_nat_to_int(x_15);
x_81 = lean_int_add(x_80, x_2);
lean_dec(x_80);
x_82 = l_Int_toNat(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_14);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_12);
x_85 = lean_array_uset(x_10, x_5, x_84);
x_5 = x_20;
x_6 = x_85;
goto _start;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_nat_to_int(x_14);
x_88 = lean_int_add(x_87, x_2);
lean_dec(x_87);
x_89 = l_Int_toNat(x_88);
lean_dec(x_88);
if (x_18 == 0)
{
x_21 = x_89;
goto block_51;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_16);
lean_dec(x_13);
x_90 = lean_nat_to_int(x_15);
x_91 = lean_int_add(x_90, x_2);
lean_dec(x_90);
x_92 = l_Int_toNat(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_12);
x_95 = lean_array_uset(x_10, x_5, x_94);
x_5 = x_20;
x_6 = x_95;
goto _start;
}
}
block_51:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_nat_dec_lt(x_15, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_24 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_25 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3;
x_32 = lean_string_append(x_30, x_31);
lean_inc(x_3);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5;
x_38 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6;
x_39 = lean_unsigned_to_nat(83u);
x_40 = lean_unsigned_to_nat(6u);
x_41 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_37, x_38, x_39, x_40, x_36);
lean_dec(x_36);
x_42 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_41);
if (lean_is_scalar(x_16)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_16;
}
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_42);
if (lean_is_scalar(x_13)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_13;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_12);
x_45 = lean_array_uset(x_10, x_5, x_44);
x_5 = x_20;
x_6 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_22);
if (lean_is_scalar(x_16)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_16;
}
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_15);
if (lean_is_scalar(x_13)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_13;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_12);
x_49 = lean_array_uset(x_10, x_5, x_48);
x_5 = x_20;
x_6 = x_49;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_9 = lean_array_uget(x_7, x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_7, x_6, x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 x_15 = x_9;
} else {
 lean_dec_ref(x_9);
 x_15 = lean_box(0);
}
x_16 = 1;
x_17 = lean_usize_add(x_6, x_16);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(0, 3, 0);
} else {
 x_19 = x_15;
}
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_11, x_6, x_19);
x_6 = x_17;
x_7 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_23 = x_14;
} else {
 lean_dec_ref(x_14);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_name_eq(x_24, x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_22);
if (lean_is_scalar(x_15)) {
 x_28 = lean_alloc_ctor(0, 3, 0);
} else {
 x_28 = x_15;
}
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_13);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_uset(x_11, x_6, x_28);
x_6 = x_17;
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_71; 
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_31 = x_22;
} else {
 lean_dec_ref(x_22);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_34 = x_25;
} else {
 lean_dec_ref(x_25);
 x_34 = lean_box(0);
}
x_35 = lean_nat_dec_lt(x_4, x_32);
x_71 = lean_nat_dec_lt(x_4, x_33);
if (x_35 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
x_73 = lean_nat_dec_lt(x_32, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_74 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_75 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1;
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_77 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2;
x_78 = lean_string_append(x_76, x_77);
x_79 = l___private_Init_Data_Repr_0__Nat_reprFast(x_72);
x_80 = lean_string_append(x_78, x_79);
lean_dec(x_79);
x_81 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3;
x_82 = lean_string_append(x_80, x_81);
lean_inc(x_4);
x_83 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
x_86 = lean_string_append(x_84, x_85);
x_87 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5;
x_88 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6;
x_89 = lean_unsigned_to_nat(83u);
x_90 = lean_unsigned_to_nat(6u);
x_91 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_87, x_88, x_89, x_90, x_86);
lean_dec(x_86);
x_92 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_91);
if (x_71 == 0)
{
x_36 = x_92;
goto block_70;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_15);
x_93 = lean_nat_to_int(x_33);
x_94 = lean_int_add(x_93, x_3);
lean_dec(x_93);
x_95 = l_Int_toNat(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_24);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_12);
lean_ctor_set(x_99, 1, x_13);
lean_ctor_set(x_99, 2, x_98);
x_100 = lean_array_uset(x_11, x_6, x_99);
x_6 = x_17;
x_7 = x_100;
goto _start;
}
}
else
{
lean_dec(x_72);
if (x_71 == 0)
{
x_36 = x_32;
goto block_70;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_15);
x_102 = lean_nat_to_int(x_33);
x_103 = lean_int_add(x_102, x_3);
lean_dec(x_102);
x_104 = l_Int_toNat(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_32);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_24);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_12);
lean_ctor_set(x_108, 1, x_13);
lean_ctor_set(x_108, 2, x_107);
x_109 = lean_array_uset(x_11, x_6, x_108);
x_6 = x_17;
x_7 = x_109;
goto _start;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_nat_to_int(x_32);
x_112 = lean_int_add(x_111, x_3);
lean_dec(x_111);
x_113 = l_Int_toNat(x_112);
lean_dec(x_112);
if (x_71 == 0)
{
x_36 = x_113;
goto block_70;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_15);
x_114 = lean_nat_to_int(x_33);
x_115 = lean_int_add(x_114, x_3);
lean_dec(x_114);
x_116 = l_Int_toNat(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_24);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_12);
lean_ctor_set(x_120, 1, x_13);
lean_ctor_set(x_120, 2, x_119);
x_121 = lean_array_uset(x_11, x_6, x_120);
x_6 = x_17;
x_7 = x_121;
goto _start;
}
}
block_70:
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_nat_dec_lt(x_33, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_37);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3;
x_47 = lean_string_append(x_45, x_46);
lean_inc(x_4);
x_48 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5;
x_53 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6;
x_54 = lean_unsigned_to_nat(83u);
x_55 = lean_unsigned_to_nat(6u);
x_56 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_52, x_53, x_54, x_55, x_51);
lean_dec(x_51);
x_57 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_56);
if (lean_is_scalar(x_34)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_34;
}
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_57);
if (lean_is_scalar(x_31)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_31;
}
lean_ctor_set(x_59, 0, x_24);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_23)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_23;
}
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_15)) {
 x_61 = lean_alloc_ctor(0, 3, 0);
} else {
 x_61 = x_15;
}
lean_ctor_set(x_61, 0, x_12);
lean_ctor_set(x_61, 1, x_13);
lean_ctor_set(x_61, 2, x_60);
x_62 = lean_array_uset(x_11, x_6, x_61);
x_6 = x_17;
x_7 = x_62;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_37);
if (lean_is_scalar(x_34)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_34;
}
lean_ctor_set(x_64, 0, x_36);
lean_ctor_set(x_64, 1, x_33);
if (lean_is_scalar(x_31)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_31;
}
lean_ctor_set(x_65, 0, x_24);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_23)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_23;
}
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_15)) {
 x_67 = lean_alloc_ctor(0, 3, 0);
} else {
 x_67 = x_15;
}
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_13);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_array_uset(x_11, x_6, x_67);
x_6 = x_17;
x_7 = x_68;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 1;
x_9 = 0;
x_10 = l_String_Range_overlaps(x_1, x_7, x_8, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_name_eq(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
size_t x_15; size_t x_16; 
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = 1;
x_20 = 0;
x_21 = l_String_Range_overlaps(x_2, x_18, x_19, x_20);
lean_dec(x_18);
if (x_21 == 0)
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = lean_usize_add(x_4, x_22);
x_4 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_nat_to_int(x_10);
x_12 = l_String_Range_bsize(x_2);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_sub(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_15, x_3);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 3);
lean_inc(x_18);
x_19 = lean_array_size(x_18);
x_20 = 0;
lean_inc(x_15);
lean_inc(x_2);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1(x_2, x_14, x_15, x_19, x_20, x_18);
x_22 = lean_ctor_get(x_4, 4);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
lean_dec(x_4);
if (x_16 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_nat_dec_lt(x_3, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_36 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3;
x_43 = lean_string_append(x_41, x_42);
lean_inc(x_15);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5;
x_49 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6;
x_50 = lean_unsigned_to_nat(83u);
x_51 = lean_unsigned_to_nat(6u);
x_52 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_48, x_49, x_50, x_51, x_47);
lean_dec(x_47);
x_53 = l_panic___at_Lean_Parser_ParserState_mkUnexpectedTokenErrors___spec__1(x_52);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_54; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_6);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_6);
lean_ctor_set(x_55, 2, x_17);
lean_ctor_set(x_55, 3, x_21);
lean_ctor_set(x_55, 4, x_22);
lean_ctor_set_uint8(x_55, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_55, sizeof(void*)*5 + 1, x_24);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_6, 0);
lean_inc(x_57);
lean_dec(x_6);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_17);
lean_ctor_set(x_59, 3, x_21);
lean_ctor_set(x_59, 4, x_22);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 1, x_24);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_6, 0);
lean_inc(x_61);
lean_dec(x_6);
x_25 = x_53;
x_26 = x_61;
goto block_32;
}
}
else
{
lean_dec(x_33);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_62; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_6);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_6);
lean_ctor_set(x_63, 2, x_17);
lean_ctor_set(x_63, 3, x_21);
lean_ctor_set(x_63, 4, x_22);
lean_ctor_set_uint8(x_63, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_63, sizeof(void*)*5 + 1, x_24);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_6, 0);
lean_inc(x_65);
lean_dec(x_6);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_67, 0, x_3);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_17);
lean_ctor_set(x_67, 3, x_21);
lean_ctor_set(x_67, 4, x_22);
lean_ctor_set_uint8(x_67, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_67, sizeof(void*)*5 + 1, x_24);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_6, 0);
lean_inc(x_69);
lean_dec(x_6);
x_25 = x_3;
x_26 = x_69;
goto block_32;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_nat_to_int(x_3);
x_71 = lean_int_add(x_70, x_14);
lean_dec(x_70);
x_72 = l_Int_toNat(x_71);
lean_dec(x_71);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_73; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_6);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_6);
lean_ctor_set(x_74, 2, x_17);
lean_ctor_set(x_74, 3, x_21);
lean_ctor_set(x_74, 4, x_22);
lean_ctor_set_uint8(x_74, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_74, sizeof(void*)*5 + 1, x_24);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_6, 0);
lean_inc(x_76);
lean_dec(x_6);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_17);
lean_ctor_set(x_78, 3, x_21);
lean_ctor_set(x_78, 4, x_22);
lean_ctor_set_uint8(x_78, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_78, sizeof(void*)*5 + 1, x_24);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_6, 0);
lean_inc(x_80);
lean_dec(x_6);
x_25 = x_72;
x_26 = x_80;
goto block_32;
}
}
block_32:
{
size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_array_size(x_26);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__2(x_5, x_2, x_14, x_15, x_27, x_20, x_26);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 1, x_24);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = 1;
x_8 = l_String_Range_contains(x_3, x_5, x_7);
if (lean_obj_tag(x_6) == 0)
{
if (x_8 == 0)
{
uint8_t x_25; 
x_25 = 0;
x_9 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_28 = lean_array_get_size(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
if (x_8 == 0)
{
uint8_t x_31; 
x_31 = 0;
x_9 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
return x_32;
}
}
else
{
if (x_8 == 0)
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_35 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__4(x_1, x_3, x_27, x_33, x_34);
lean_dec(x_27);
x_9 = x_35;
goto block_24;
}
else
{
lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
return x_36;
}
}
}
block_24:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
if (x_9 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Server_FileWorker_applyEditToHint_x3f___lambda__1(x_4, x_3, x_5, x_2, x_1, x_6, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__3(x_3, x_10, x_17, x_18);
lean_dec(x_10);
if (x_19 == 0)
{
if (x_9 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Server_FileWorker_applyEditToHint_x3f___lambda__1(x_4, x_3, x_5, x_2, x_1, x_6, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__2(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__4(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_applyEditToHint_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_applyEditToHint_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Server", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FileWorker", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("InlayHintState", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__1;
x_2 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__2;
x_3 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__3;
x_4 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instTypeNameInlayHintState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737_;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedInlayHintState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_InlayHintState_init___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_InlayHintState_init___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_InlayHintState_init() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_InlayHintState_init___closed__2;
return x_1;
}
}
static lean_object* _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_instInhabitedRequestError;
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__2;
x_5 = lean_panic_fn(x_4, x_1);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
}
}
static lean_object* _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonad(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__2;
x_2 = l_StateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__3;
x_3 = l_instInhabitedOfMonad___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__4;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_List_reverse___rarg(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3(x_1, x_2, x_3, x_13, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_18);
{
lean_object* _tmp_3 = x_14;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_5 = x_19;
lean_object* _tmp_7 = x_17;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_21; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3(x_1, x_2, x_3, x_25, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_5);
x_4 = x_26;
x_5 = x_32;
x_6 = x_31;
x_8 = x_29;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_36 = x_27;
} else {
 lean_dec_ref(x_27);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.InfoUtils", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.InfoTree.visitM.go", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected context-free info tree node", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__1;
x_2 = l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(62u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_8, x_3);
x_3 = x_10;
x_4 = x_9;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__4;
x_13 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4(x_12, x_5, x_6, x_7);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
else
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_17, x_3);
x_3 = x_19;
x_4 = x_18;
goto _start;
}
case 1:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_25 = lean_apply_6(x_1, x_22, x_23, x_24, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_apply_7(x_2, x_22, x_23, x_24, x_31, x_30, x_6, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_ctor_set(x_3, 0, x_36);
lean_ctor_set(x_34, 0, x_3);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
lean_ctor_set(x_3, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_32, 0, x_39);
return x_32;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
lean_ctor_set(x_3, 0, x_42);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_free_object(x_3);
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
return x_32;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_32, 0);
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_32);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_dec(x_25);
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_dec(x_26);
lean_inc(x_22);
x_53 = l_Lean_Elab_Info_updateContext_x3f(x_3, x_23);
x_54 = l_Lean_PersistentArray_toList___rarg(x_24);
x_55 = lean_box(0);
lean_inc(x_6);
lean_inc(x_2);
x_56 = l_List_mapM_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__5(x_1, x_2, x_53, x_54, x_55, x_52, x_6, x_51);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_apply_7(x_2, x_22, x_23, x_24, x_59, x_60, x_6, x_58);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_63, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_61, 0, x_70);
return x_61;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_61, 0);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_61);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_56);
if (x_83 == 0)
{
return x_56;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_56, 0);
x_85 = lean_ctor_get(x_56, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_56);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_3);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_25);
if (x_87 == 0)
{
return x_25;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_25, 0);
x_89 = lean_ctor_get(x_25, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_25);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_3, 0);
lean_inc(x_91);
lean_dec(x_3);
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
x_94 = lean_apply_6(x_1, x_91, x_92, x_93, x_5, x_6, x_7);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_1);
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_box(0);
x_101 = lean_apply_7(x_2, x_91, x_92, x_93, x_100, x_99, x_6, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_107 = x_102;
} else {
 lean_dec_ref(x_102);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_105);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_104;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_103);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_101, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_113 = x_101;
} else {
 lean_dec_ref(x_101);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_94, 1);
lean_inc(x_115);
lean_dec(x_94);
x_116 = lean_ctor_get(x_95, 1);
lean_inc(x_116);
lean_dec(x_95);
lean_inc(x_91);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_91);
x_118 = l_Lean_Elab_Info_updateContext_x3f(x_117, x_92);
x_119 = l_Lean_PersistentArray_toList___rarg(x_93);
x_120 = lean_box(0);
lean_inc(x_6);
lean_inc(x_2);
x_121 = l_List_mapM_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__5(x_1, x_2, x_118, x_119, x_120, x_116, x_6, x_115);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_apply_7(x_2, x_91, x_92, x_93, x_124, x_125, x_6, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_130);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_129;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_128);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_126, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_126, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_138 = x_126;
} else {
 lean_dec_ref(x_126);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_6);
lean_dec(x_2);
x_140 = lean_ctor_get(x_121, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_121, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_142 = x_121;
} else {
 lean_dec_ref(x_121);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_94, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_94, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_146 = x_94;
} else {
 lean_dec_ref(x_94);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
default: 
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_5);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_7);
return x_150;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_1, x_2, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2___lambda__1___boxed), 8, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_InlayHint_resolveDeferred), 6, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_13, x_14, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_push(x_4, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_push(x_4, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = l_Lean_Server_RequestError_ofIoError(x_30);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = l_Lean_Server_RequestError_ofIoError(x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
return x_38;
}
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_uget(x_11, x_3);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_12);
x_15 = l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__1;
x_16 = l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__2;
lean_inc(x_6);
x_17 = l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2(x_15, x_16, x_13, x_14, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_box(0);
x_3 = x_22;
x_4 = x_23;
x_5 = x_20;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_5, x_4, x_11);
lean_inc(x_1);
lean_inc(x_2);
x_13 = l_Lean_Elab_InlayHintInfo_toLspInlayHint(x_2, x_1, x_10, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_18 = lean_array_uset(x_12, x_4, x_14);
x_4 = x_17;
x_5 = x_18;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = l_Lean_Server_RequestError_ofIoError(x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = l_Lean_Server_RequestError_ofIoError(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_5, x_4, x_11);
lean_inc(x_1);
lean_inc(x_2);
x_13 = l_Lean_Elab_InlayHintInfo_toLspInlayHint(x_2, x_1, x_10, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_18 = lean_array_uset(x_12, x_4, x_14);
x_4 = x_17;
x_5 = x_18;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = l_Lean_Server_RequestError_ofIoError(x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = l_Lean_Server_RequestError_ofIoError(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 1;
x_10 = l_String_Range_contains(x_1, x_8, x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_5, x_4, x_11);
lean_inc(x_1);
lean_inc(x_2);
x_13 = l_Lean_Elab_InlayHintInfo_toLspInlayHint(x_2, x_1, x_10, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_18 = lean_array_uset(x_12, x_4, x_14);
x_4 = x_17;
x_5 = x_18;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = l_Lean_Server_RequestError_ofIoError(x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = l_Lean_Server_RequestError_ofIoError(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 0;
x_10 = l_String_Range_contains(x_1, x_8, x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 0;
x_10 = l_String_Range_contains(x_1, x_8, x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 0;
x_10 = l_String_Range_contains(x_1, x_8, x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 0;
x_10 = l_String_Range_contains(x_1, x_8, x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("finishedSnaps >= oldFinishedSnaps\n  -- VS Code emits inlay hint requests *every time the user scrolls*. This is reasonably expensive,\n  -- so in addition to re-using old inlay hints from parts of the file that haven't been processed\n  -- yet, we also re-use old inlay hints from parts of the file that have been processed already\n  -- with the current state of the document.\n  ", 377, 377);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_handleInlayHints___closed__1;
x_2 = l_Lean_Server_FileWorker_handleInlayHints___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.FileWorker.handleInlayHints", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5;
x_2 = l_Lean_Server_FileWorker_handleInlayHints___closed__4;
x_3 = lean_unsigned_to_nat(133u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Server_FileWorker_handleInlayHints___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static size_t _init_l_Lean_Server_FileWorker_handleInlayHints___closed__6() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_FileMap_lspRangeToUtf8Range(x_8, x_9);
lean_inc(x_3);
x_11 = l_Lean_Server_RequestContext_srcSearchPath(x_3);
x_12 = lean_io_mono_ms_now(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_326 = lean_ctor_get(x_6, 2);
lean_inc(x_326);
lean_dec(x_6);
x_327 = lean_ctor_get(x_3, 5);
lean_inc(x_327);
x_328 = l_Lean_Server_RequestCancellationToken_cancellationTask(x_327);
lean_dec(x_327);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
if (lean_obj_tag(x_15) == 0)
{
uint32_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_13);
x_330 = 0;
x_331 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg(x_326, x_330, x_329, x_14);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_16 = x_332;
x_17 = x_333;
goto block_325;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint32_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_334 = lean_ctor_get(x_15, 0);
lean_inc(x_334);
x_335 = lean_nat_sub(x_13, x_334);
lean_dec(x_334);
lean_dec(x_13);
x_336 = lean_unsigned_to_nat(3000u);
x_337 = lean_nat_sub(x_336, x_335);
lean_dec(x_335);
x_338 = lean_uint32_of_nat(x_337);
lean_dec(x_337);
x_339 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg(x_326, x_338, x_329, x_14);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_16 = x_340;
x_17 = x_341;
goto block_325;
}
block_325:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_array_mk(x_19);
x_24 = lean_array_get_size(x_23);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_nat_dec_le(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_27 = l_Lean_Server_FileWorker_handleInlayHints___closed__5;
x_28 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1(x_27, x_3, x_17);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; size_t x_44; lean_object* x_45; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_25, x_29);
x_31 = lean_nat_dec_lt(x_30, x_24);
x_32 = lean_nat_sub(x_24, x_29);
x_33 = lean_nat_dec_lt(x_32, x_24);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_35 = x_2;
} else {
 lean_dec_ref(x_2);
 x_35 = lean_box(0);
}
x_36 = lean_array_get_size(x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
x_39 = lean_array_get_size(x_23);
lean_inc(x_23);
x_40 = l_Array_toSubarray___rarg(x_23, x_25, x_39);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
if (x_31 == 0)
{
lean_dec(x_30);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_23);
lean_free_object(x_18);
if (x_38 == 0)
{
lean_object* x_167; 
lean_dec(x_36);
lean_dec(x_34);
x_167 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_167;
goto block_166;
}
else
{
uint8_t x_168; 
x_168 = lean_nat_dec_le(x_36, x_36);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_36);
lean_dec(x_34);
x_169 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_169;
goto block_166;
}
else
{
size_t x_170; size_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = 0;
x_171 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_172 = l_Lean_Server_FileWorker_handleInlayHints___closed__7;
x_173 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_174 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__11(x_172, x_34, x_170, x_171, x_173);
lean_dec(x_34);
x_45 = x_174;
goto block_166;
}
}
}
else
{
if (x_38 == 0)
{
lean_object* x_175; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_23);
lean_free_object(x_18);
x_175 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_175;
goto block_166;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_array_fget(x_23, x_32);
lean_dec(x_32);
lean_dec(x_23);
x_177 = l_Lean_Server_Snapshots_Snapshot_endPos(x_176);
lean_dec(x_176);
lean_ctor_set(x_18, 1, x_177);
lean_ctor_set(x_18, 0, x_37);
x_178 = lean_nat_dec_le(x_36, x_36);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_18);
lean_dec(x_36);
lean_dec(x_34);
x_179 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_179;
goto block_166;
}
else
{
size_t x_180; size_t x_181; lean_object* x_182; lean_object* x_183; 
x_180 = 0;
x_181 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_182 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_183 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__12(x_18, x_34, x_180, x_181, x_182);
lean_dec(x_34);
lean_dec(x_18);
x_45 = x_183;
goto block_166;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_array_fget(x_23, x_30);
lean_dec(x_30);
x_185 = l_Lean_Server_Snapshots_Snapshot_endPos(x_184);
lean_dec(x_184);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_23);
if (x_38 == 0)
{
lean_object* x_186; 
lean_dec(x_185);
lean_dec(x_36);
lean_dec(x_34);
lean_free_object(x_18);
x_186 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_186;
goto block_166;
}
else
{
uint8_t x_187; 
lean_ctor_set(x_18, 1, x_37);
lean_ctor_set(x_18, 0, x_185);
x_187 = lean_nat_dec_le(x_36, x_36);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_18);
lean_dec(x_36);
lean_dec(x_34);
x_188 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_188;
goto block_166;
}
else
{
size_t x_189; size_t x_190; lean_object* x_191; lean_object* x_192; 
x_189 = 0;
x_190 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_191 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_192 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__13(x_18, x_34, x_189, x_190, x_191);
lean_dec(x_34);
lean_dec(x_18);
x_45 = x_192;
goto block_166;
}
}
}
else
{
if (x_38 == 0)
{
lean_object* x_193; 
lean_dec(x_185);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_23);
lean_free_object(x_18);
x_193 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_193;
goto block_166;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_array_fget(x_23, x_32);
lean_dec(x_32);
lean_dec(x_23);
x_195 = l_Lean_Server_Snapshots_Snapshot_endPos(x_194);
lean_dec(x_194);
lean_ctor_set(x_18, 1, x_195);
lean_ctor_set(x_18, 0, x_185);
x_196 = lean_nat_dec_le(x_36, x_36);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_18);
lean_dec(x_36);
lean_dec(x_34);
x_197 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_45 = x_197;
goto block_166;
}
else
{
size_t x_198; size_t x_199; lean_object* x_200; lean_object* x_201; 
x_198 = 0;
x_199 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_200 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_201 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__14(x_18, x_34, x_198, x_199, x_200);
lean_dec(x_34);
lean_dec(x_18);
x_45 = x_201;
goto block_166;
}
}
}
}
block_166:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_box(0);
x_47 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
lean_inc(x_3);
x_48 = l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6(x_40, x_42, x_44, x_46, x_47, x_3, x_17);
lean_dec(x_40);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; size_t x_57; 
x_52 = lean_ctor_get(x_49, 1);
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = l_Array_append___rarg(x_52, x_45);
lean_dec(x_45);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_37, x_55);
x_57 = 0;
if (x_56 == 0)
{
size_t x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_10);
x_58 = l_Lean_Server_FileWorker_handleInlayHints___closed__6;
x_59 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7(x_8, x_11, x_58, x_57, x_47, x_3, x_50);
lean_dec(x_3);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
if (lean_is_scalar(x_35)) {
 x_64 = lean_alloc_ctor(0, 3, 0);
} else {
 x_64 = x_35;
}
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_24);
lean_ctor_set(x_64, 2, x_15);
lean_ctor_set(x_49, 1, x_64);
lean_ctor_set(x_49, 0, x_62);
lean_ctor_set(x_59, 0, x_49);
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_68);
if (lean_is_scalar(x_35)) {
 x_69 = lean_alloc_ctor(0, 3, 0);
} else {
 x_69 = x_35;
}
lean_ctor_set(x_69, 0, x_54);
lean_ctor_set(x_69, 1, x_24);
lean_ctor_set(x_69, 2, x_15);
lean_ctor_set(x_49, 1, x_69);
lean_ctor_set(x_49, 0, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_49);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_54);
lean_free_object(x_49);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
return x_59;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_59, 0);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_59);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_55, x_55);
if (x_75 == 0)
{
size_t x_76; lean_object* x_77; 
lean_dec(x_55);
lean_dec(x_10);
x_76 = l_Lean_Server_FileWorker_handleInlayHints___closed__6;
x_77 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8(x_8, x_11, x_76, x_57, x_47, x_3, x_50);
lean_dec(x_3);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
if (lean_is_scalar(x_35)) {
 x_82 = lean_alloc_ctor(0, 3, 0);
} else {
 x_82 = x_35;
}
lean_ctor_set(x_82, 0, x_54);
lean_ctor_set(x_82, 1, x_24);
lean_ctor_set(x_82, 2, x_15);
lean_ctor_set(x_49, 1, x_82);
lean_ctor_set(x_49, 0, x_80);
lean_ctor_set(x_77, 0, x_49);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_35)) {
 x_87 = lean_alloc_ctor(0, 3, 0);
} else {
 x_87 = x_35;
}
lean_ctor_set(x_87, 0, x_54);
lean_ctor_set(x_87, 1, x_24);
lean_ctor_set(x_87, 2, x_15);
lean_ctor_set(x_49, 1, x_87);
lean_ctor_set(x_49, 0, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_49);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_54);
lean_free_object(x_49);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
x_89 = !lean_is_exclusive(x_77);
if (x_89 == 0)
{
return x_77;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_77, 0);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_77);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
size_t x_93; lean_object* x_94; size_t x_95; lean_object* x_96; 
x_93 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_94 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9(x_10, x_54, x_57, x_93, x_47);
lean_dec(x_10);
x_95 = lean_array_size(x_94);
x_96 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10(x_8, x_11, x_95, x_57, x_94, x_3, x_50);
lean_dec(x_3);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_100);
if (lean_is_scalar(x_35)) {
 x_101 = lean_alloc_ctor(0, 3, 0);
} else {
 x_101 = x_35;
}
lean_ctor_set(x_101, 0, x_54);
lean_ctor_set(x_101, 1, x_24);
lean_ctor_set(x_101, 2, x_15);
lean_ctor_set(x_49, 1, x_101);
lean_ctor_set(x_49, 0, x_99);
lean_ctor_set(x_96, 0, x_49);
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_96, 0);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_105);
if (lean_is_scalar(x_35)) {
 x_106 = lean_alloc_ctor(0, 3, 0);
} else {
 x_106 = x_35;
}
lean_ctor_set(x_106, 0, x_54);
lean_ctor_set(x_106, 1, x_24);
lean_ctor_set(x_106, 2, x_15);
lean_ctor_set(x_49, 1, x_106);
lean_ctor_set(x_49, 0, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_49);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_dec(x_54);
lean_free_object(x_49);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
x_108 = !lean_is_exclusive(x_96);
if (x_108 == 0)
{
return x_96;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_96, 0);
x_110 = lean_ctor_get(x_96, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_96);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; size_t x_116; 
x_112 = lean_ctor_get(x_49, 1);
lean_inc(x_112);
lean_dec(x_49);
x_113 = l_Array_append___rarg(x_112, x_45);
lean_dec(x_45);
x_114 = lean_array_get_size(x_113);
x_115 = lean_nat_dec_lt(x_37, x_114);
x_116 = 0;
if (x_115 == 0)
{
size_t x_117; lean_object* x_118; 
lean_dec(x_114);
lean_dec(x_10);
x_117 = l_Lean_Server_FileWorker_handleInlayHints___closed__6;
x_118 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7(x_8, x_11, x_117, x_116, x_47, x_3, x_50);
lean_dec(x_3);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
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
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_119);
x_123 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_123);
if (lean_is_scalar(x_35)) {
 x_124 = lean_alloc_ctor(0, 3, 0);
} else {
 x_124 = x_35;
}
lean_ctor_set(x_124, 0, x_113);
lean_ctor_set(x_124, 1, x_24);
lean_ctor_set(x_124, 2, x_15);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_121)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_121;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_120);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_113);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
x_127 = lean_ctor_get(x_118, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_129 = x_118;
} else {
 lean_dec_ref(x_118);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_le(x_114, x_114);
if (x_131 == 0)
{
size_t x_132; lean_object* x_133; 
lean_dec(x_114);
lean_dec(x_10);
x_132 = l_Lean_Server_FileWorker_handleInlayHints___closed__6;
x_133 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8(x_8, x_11, x_132, x_116, x_47, x_3, x_50);
lean_dec(x_3);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_134);
x_138 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_138);
if (lean_is_scalar(x_35)) {
 x_139 = lean_alloc_ctor(0, 3, 0);
} else {
 x_139 = x_35;
}
lean_ctor_set(x_139, 0, x_113);
lean_ctor_set(x_139, 1, x_24);
lean_ctor_set(x_139, 2, x_15);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_135);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_113);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
x_142 = lean_ctor_get(x_133, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_144 = x_133;
} else {
 lean_dec_ref(x_133);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
size_t x_146; lean_object* x_147; size_t x_148; lean_object* x_149; 
x_146 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_147 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9(x_10, x_113, x_116, x_146, x_47);
lean_dec(x_10);
x_148 = lean_array_size(x_147);
x_149 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10(x_8, x_11, x_148, x_116, x_147, x_3, x_50);
lean_dec(x_3);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_153, 0, x_150);
x_154 = lean_unbox(x_21);
lean_dec(x_21);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_154);
if (lean_is_scalar(x_35)) {
 x_155 = lean_alloc_ctor(0, 3, 0);
} else {
 x_155 = x_35;
}
lean_ctor_set(x_155, 0, x_113);
lean_ctor_set(x_155, 1, x_24);
lean_ctor_set(x_155, 2, x_15);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_151);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_113);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
x_158 = lean_ctor_get(x_149, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_160 = x_149;
} else {
 lean_dec_ref(x_149);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_48);
if (x_162 == 0)
{
return x_48;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_48, 0);
x_164 = lean_ctor_get(x_48, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_48);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_18, 1);
lean_inc(x_202);
lean_dec(x_18);
x_203 = lean_array_mk(x_19);
x_204 = lean_array_get_size(x_203);
x_205 = lean_ctor_get(x_2, 1);
lean_inc(x_205);
x_206 = lean_nat_dec_le(x_205, x_204);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_207 = l_Lean_Server_FileWorker_handleInlayHints___closed__5;
x_208 = l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1(x_207, x_3, x_17);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; size_t x_222; lean_object* x_223; size_t x_224; lean_object* x_225; 
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_sub(x_205, x_209);
x_211 = lean_nat_dec_lt(x_210, x_204);
x_212 = lean_nat_sub(x_204, x_209);
x_213 = lean_nat_dec_lt(x_212, x_204);
x_214 = lean_ctor_get(x_2, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_215 = x_2;
} else {
 lean_dec_ref(x_2);
 x_215 = lean_box(0);
}
x_216 = lean_array_get_size(x_214);
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_dec_lt(x_217, x_216);
x_219 = lean_array_get_size(x_203);
lean_inc(x_203);
x_220 = l_Array_toSubarray___rarg(x_203, x_205, x_219);
x_221 = lean_ctor_get(x_220, 2);
lean_inc(x_221);
x_222 = lean_usize_of_nat(x_221);
lean_dec(x_221);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
x_224 = lean_usize_of_nat(x_223);
lean_dec(x_223);
if (x_211 == 0)
{
lean_dec(x_210);
if (x_213 == 0)
{
lean_dec(x_212);
lean_dec(x_203);
if (x_218 == 0)
{
lean_object* x_287; 
lean_dec(x_216);
lean_dec(x_214);
x_287 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_287;
goto block_286;
}
else
{
uint8_t x_288; 
x_288 = lean_nat_dec_le(x_216, x_216);
if (x_288 == 0)
{
lean_object* x_289; 
lean_dec(x_216);
lean_dec(x_214);
x_289 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_289;
goto block_286;
}
else
{
size_t x_290; size_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = 0;
x_291 = lean_usize_of_nat(x_216);
lean_dec(x_216);
x_292 = l_Lean_Server_FileWorker_handleInlayHints___closed__7;
x_293 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_294 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__11(x_292, x_214, x_290, x_291, x_293);
lean_dec(x_214);
x_225 = x_294;
goto block_286;
}
}
}
else
{
if (x_218 == 0)
{
lean_object* x_295; 
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_203);
x_295 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_295;
goto block_286;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_array_fget(x_203, x_212);
lean_dec(x_212);
lean_dec(x_203);
x_297 = l_Lean_Server_Snapshots_Snapshot_endPos(x_296);
lean_dec(x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_217);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_nat_dec_le(x_216, x_216);
if (x_299 == 0)
{
lean_object* x_300; 
lean_dec(x_298);
lean_dec(x_216);
lean_dec(x_214);
x_300 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_300;
goto block_286;
}
else
{
size_t x_301; size_t x_302; lean_object* x_303; lean_object* x_304; 
x_301 = 0;
x_302 = lean_usize_of_nat(x_216);
lean_dec(x_216);
x_303 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_304 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__12(x_298, x_214, x_301, x_302, x_303);
lean_dec(x_214);
lean_dec(x_298);
x_225 = x_304;
goto block_286;
}
}
}
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_array_fget(x_203, x_210);
lean_dec(x_210);
x_306 = l_Lean_Server_Snapshots_Snapshot_endPos(x_305);
lean_dec(x_305);
if (x_213 == 0)
{
lean_dec(x_212);
lean_dec(x_203);
if (x_218 == 0)
{
lean_object* x_307; 
lean_dec(x_306);
lean_dec(x_216);
lean_dec(x_214);
x_307 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_307;
goto block_286;
}
else
{
lean_object* x_308; uint8_t x_309; 
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_217);
x_309 = lean_nat_dec_le(x_216, x_216);
if (x_309 == 0)
{
lean_object* x_310; 
lean_dec(x_308);
lean_dec(x_216);
lean_dec(x_214);
x_310 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_310;
goto block_286;
}
else
{
size_t x_311; size_t x_312; lean_object* x_313; lean_object* x_314; 
x_311 = 0;
x_312 = lean_usize_of_nat(x_216);
lean_dec(x_216);
x_313 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_314 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__13(x_308, x_214, x_311, x_312, x_313);
lean_dec(x_214);
lean_dec(x_308);
x_225 = x_314;
goto block_286;
}
}
}
else
{
if (x_218 == 0)
{
lean_object* x_315; 
lean_dec(x_306);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_212);
lean_dec(x_203);
x_315 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_315;
goto block_286;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_316 = lean_array_fget(x_203, x_212);
lean_dec(x_212);
lean_dec(x_203);
x_317 = l_Lean_Server_Snapshots_Snapshot_endPos(x_316);
lean_dec(x_316);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_306);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_nat_dec_le(x_216, x_216);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_318);
lean_dec(x_216);
lean_dec(x_214);
x_320 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_225 = x_320;
goto block_286;
}
else
{
size_t x_321; size_t x_322; lean_object* x_323; lean_object* x_324; 
x_321 = 0;
x_322 = lean_usize_of_nat(x_216);
lean_dec(x_216);
x_323 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_324 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__14(x_318, x_214, x_321, x_322, x_323);
lean_dec(x_214);
lean_dec(x_318);
x_225 = x_324;
goto block_286;
}
}
}
}
block_286:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_box(0);
x_227 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
lean_inc(x_3);
x_228 = l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6(x_220, x_222, x_224, x_226, x_227, x_3, x_17);
lean_dec(x_220);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; size_t x_236; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
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
x_233 = l_Array_append___rarg(x_231, x_225);
lean_dec(x_225);
x_234 = lean_array_get_size(x_233);
x_235 = lean_nat_dec_lt(x_217, x_234);
x_236 = 0;
if (x_235 == 0)
{
size_t x_237; lean_object* x_238; 
lean_dec(x_234);
lean_dec(x_10);
x_237 = l_Lean_Server_FileWorker_handleInlayHints___closed__6;
x_238 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7(x_8, x_11, x_237, x_236, x_227, x_3, x_230);
lean_dec(x_3);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
x_242 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_242, 0, x_239);
x_243 = lean_unbox(x_202);
lean_dec(x_202);
lean_ctor_set_uint8(x_242, sizeof(void*)*1, x_243);
if (lean_is_scalar(x_215)) {
 x_244 = lean_alloc_ctor(0, 3, 0);
} else {
 x_244 = x_215;
}
lean_ctor_set(x_244, 0, x_233);
lean_ctor_set(x_244, 1, x_204);
lean_ctor_set(x_244, 2, x_15);
if (lean_is_scalar(x_232)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_232;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
if (lean_is_scalar(x_241)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_241;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_240);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_215);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_15);
x_247 = lean_ctor_get(x_238, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_238, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_249 = x_238;
} else {
 lean_dec_ref(x_238);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
uint8_t x_251; 
x_251 = lean_nat_dec_le(x_234, x_234);
if (x_251 == 0)
{
size_t x_252; lean_object* x_253; 
lean_dec(x_234);
lean_dec(x_10);
x_252 = l_Lean_Server_FileWorker_handleInlayHints___closed__6;
x_253 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8(x_8, x_11, x_252, x_236, x_227, x_3, x_230);
lean_dec(x_3);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
x_257 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_257, 0, x_254);
x_258 = lean_unbox(x_202);
lean_dec(x_202);
lean_ctor_set_uint8(x_257, sizeof(void*)*1, x_258);
if (lean_is_scalar(x_215)) {
 x_259 = lean_alloc_ctor(0, 3, 0);
} else {
 x_259 = x_215;
}
lean_ctor_set(x_259, 0, x_233);
lean_ctor_set(x_259, 1, x_204);
lean_ctor_set(x_259, 2, x_15);
if (lean_is_scalar(x_232)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_232;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_259);
if (lean_is_scalar(x_256)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_256;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_255);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_215);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_15);
x_262 = lean_ctor_get(x_253, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_253, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_264 = x_253;
} else {
 lean_dec_ref(x_253);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
else
{
size_t x_266; lean_object* x_267; size_t x_268; lean_object* x_269; 
x_266 = lean_usize_of_nat(x_234);
lean_dec(x_234);
x_267 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9(x_10, x_233, x_236, x_266, x_227);
lean_dec(x_10);
x_268 = lean_array_size(x_267);
x_269 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10(x_8, x_11, x_268, x_236, x_267, x_3, x_230);
lean_dec(x_3);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_272 = x_269;
} else {
 lean_dec_ref(x_269);
 x_272 = lean_box(0);
}
x_273 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_273, 0, x_270);
x_274 = lean_unbox(x_202);
lean_dec(x_202);
lean_ctor_set_uint8(x_273, sizeof(void*)*1, x_274);
if (lean_is_scalar(x_215)) {
 x_275 = lean_alloc_ctor(0, 3, 0);
} else {
 x_275 = x_215;
}
lean_ctor_set(x_275, 0, x_233);
lean_ctor_set(x_275, 1, x_204);
lean_ctor_set(x_275, 2, x_15);
if (lean_is_scalar(x_232)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_232;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_275);
if (lean_is_scalar(x_272)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_272;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_271);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_215);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_15);
x_278 = lean_ctor_get(x_269, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_269, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_280 = x_269;
} else {
 lean_dec_ref(x_269);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_225);
lean_dec(x_215);
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_282 = lean_ctor_get(x_228, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_228, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_284 = x_228;
} else {
 lean_dec_ref(x_228);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_InfoTree_visitM_x27___at_Lean_Server_FileWorker_handleInlayHints___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__7(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__8(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleInlayHints___spec__10(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__11(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__12(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__13(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_handleInlayHints___spec__14(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_9, x_8);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
x_23 = l_Lean_FileMap_lspRangeToUtf8Range(x_1, x_21);
lean_inc(x_19);
x_24 = l_Lean_Server_FileWorker_applyEditToHint_x3f(x_2, x_19, x_23, x_22);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_3);
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_16, 1, x_26);
lean_ctor_set(x_15, 1, x_16);
lean_ctor_set(x_15, 0, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; 
lean_dec(x_19);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
lean_ctor_set(x_16, 0, x_28);
lean_inc(x_4);
lean_ctor_set(x_15, 1, x_16);
lean_ctor_set(x_15, 0, x_4);
x_29 = 1;
x_30 = lean_usize_add(x_9, x_29);
x_9 = x_30;
x_10 = x_15;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = l_Lean_FileMap_lspRangeToUtf8Range(x_1, x_34);
lean_inc(x_32);
x_37 = l_Lean_Server_FileWorker_applyEditToHint_x3f(x_2, x_32, x_36, x_35);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_3);
x_38 = 1;
x_39 = lean_box(x_38);
lean_ctor_set(x_16, 1, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_16);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_32);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
lean_ctor_set(x_16, 0, x_42);
lean_inc(x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_16);
x_44 = 1;
x_45 = lean_usize_add(x_9, x_44);
x_9 = x_45;
x_10 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_51 = x_15;
} else {
 lean_dec_ref(x_15);
 x_51 = lean_box(0);
}
x_52 = l_Lean_FileMap_lspRangeToUtf8Range(x_1, x_49);
lean_inc(x_47);
x_53 = l_Lean_Server_FileWorker_applyEditToHint_x3f(x_2, x_47, x_52, x_50);
lean_dec(x_50);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_48);
lean_dec(x_3);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_12);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; 
lean_dec(x_47);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
lean_inc(x_4);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_60);
x_62 = 1;
x_63 = lean_usize_add(x_9, x_62);
x_9 = x_63;
x_10 = x_61;
goto _start;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_15, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_ctor_set(x_15, 0, x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_15);
lean_ctor_set(x_68, 1, x_16);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_12);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_16, 0);
x_71 = lean_ctor_get(x_16, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_3);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_15);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_12);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_15);
x_75 = lean_ctor_get(x_16, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_16, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_77 = x_16;
} else {
 lean_dec_ref(x_16);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_3);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_12);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_push(x_4, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_10, x_9);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_8, x_10);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_16);
lean_inc(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_11);
x_25 = lean_array_size(x_21);
x_26 = 0;
lean_inc(x_7);
lean_inc(x_5);
x_27 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__1(x_3, x_4, x_5, x_7, x_20, x_21, x_21, x_25, x_26, x_24, x_12, x_13);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_unbox(x_33);
lean_dec(x_33);
lean_inc(x_7);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___lambda__1(x_35, x_32, x_7, x_18, x_34, x_12, x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 1;
x_41 = lean_usize_add(x_10, x_40);
x_10 = x_41;
x_11 = x_39;
x_13 = x_38;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_7);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_29);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_29, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_29, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_27, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 0, x_30);
lean_ctor_set(x_27, 0, x_29);
return x_27;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 0, x_50);
lean_ctor_set(x_27, 0, x_29);
return x_27;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_dec(x_27);
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_53 = x_30;
} else {
 lean_dec_ref(x_30);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 0, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_29);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_29);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_57 = x_27;
} else {
 lean_dec_ref(x_27);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_30, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_59 = x_30;
} else {
 lean_dec_ref(x_30);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_18);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
lean_dec(x_11);
x_64 = lean_box(0);
x_65 = lean_ctor_get(x_1, 1);
x_66 = 0;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_16);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_7);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_7);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_size(x_65);
x_71 = 0;
lean_inc(x_7);
lean_inc(x_5);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__1(x_3, x_4, x_5, x_7, x_64, x_65, x_65, x_70, x_71, x_69, x_12, x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
lean_inc(x_7);
x_81 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___lambda__1(x_80, x_77, x_7, x_63, x_79, x_12, x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = 1;
x_86 = lean_usize_add(x_10, x_85);
x_10 = x_86;
x_11 = x_84;
x_13 = x_83;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_7);
lean_dec(x_5);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_88 = x_74;
} else {
 lean_dec_ref(x_74);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_90 = x_72;
} else {
 lean_dec_ref(x_72);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_75, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_92 = x_75;
} else {
 lean_dec_ref(x_75);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_91);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_63);
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_89);
return x_95;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Lean_Server_FileWorker_InlayHintState_init___closed__1;
x_12 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___closed__1;
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2(x_2, x_1, x_3, x_4, x_11, x_7, x_8, x_1, x_9, x_10, x_12, x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_inc(x_3);
x_20 = l_Lean_Server_RequestContext_srcSearchPath(x_3);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = l_System_Uri_fileUriToPath_x3f(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__1;
x_9 = x_23;
x_10 = x_4;
goto block_19;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = l_Lean_searchModuleNameOfFileName(x_25, x_20, x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_module_name_of_file(x_25, x_29, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_ctor_set(x_22, 0, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_22);
x_9 = x_33;
x_10 = x_32;
goto block_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_22);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_9 = x_36;
x_10 = x_35;
goto block_19;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_free_object(x_22);
lean_dec(x_25);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_dec(x_26);
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_27);
x_9 = x_39;
x_10 = x_37;
goto block_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_9 = x_42;
x_10 = x_37;
goto block_19;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
lean_dec(x_22);
lean_inc(x_43);
x_44 = l_Lean_searchModuleNameOfFileName(x_43, x_20, x_4);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_module_name_of_file(x_43, x_47, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_9 = x_52;
x_10 = x_50;
goto block_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_9 = x_55;
x_10 = x_54;
goto block_19;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_43);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
lean_dec(x_44);
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_58 = x_45;
} else {
 lean_dec_ref(x_45);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_9 = x_60;
x_10 = x_56;
goto block_19;
}
}
}
block_19:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Server_RequestError_ofIoError(x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2(x_2, x_1, x_8, x_15, x_3, x_10);
lean_dec(x_3);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2(x_2, x_1, x_8, x_17, x_3, x_10);
lean_dec(x_3);
lean_dec(x_17);
lean_dec(x_8);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_14 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_14, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___lambda__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_15 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14, x_15, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104_(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__2(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Array_contains___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__1(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_FileMap_lspRangeToUtf8Range(x_2, x_9);
lean_ctor_set(x_7, 0, x_10);
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_7);
x_14 = 1;
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_17 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__3(x_7, x_1, x_15, x_16);
lean_dec(x_7);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
else
{
size_t x_19; size_t x_20; 
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
goto _start;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = l_Lean_FileMap_lspRangeToUtf8Range(x_2, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_array_get_size(x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_26);
lean_dec(x_25);
x_29 = 1;
return x_29;
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_32 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__3(x_25, x_1, x_30, x_31);
lean_dec(x_25);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = 1;
return x_33;
}
else
{
size_t x_34; size_t x_35; 
x_34 = 1;
x_35 = lean_usize_add(x_4, x_34);
x_4 = x_35;
goto _start;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
x_37 = 1;
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = 0;
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_ctor_get(x_15, 2);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = lean_io_mono_ms_now(x_4);
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_5 = x_24;
x_6 = x_22;
x_7 = x_23;
goto block_12;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_27 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__4(x_2, x_16, x_17, x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = 1;
x_5 = x_30;
x_6 = x_28;
x_7 = x_29;
goto block_12;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = 0;
x_5 = x_33;
x_6 = x_31;
x_7 = x_32;
goto block_12;
}
}
block_12:
{
if (x_5 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___spec__4(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_6 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(x_1, x_5, x_3, x_8);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleInlayHintsDidChange(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot parse request params: ", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonInlayHintParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_11544_(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
x_12 = lean_string_append(x_10, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Json_compress(x_1);
x_17 = l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_15);
lean_dec(x_15);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4;
x_23 = lean_string_append(x_21, x_22);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonInlayHint____x40_Lean_Data_Lsp_LanguageFeatures___hyg_12835_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4(x_4);
x_9 = l_liftExcept___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__5(x_8, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_1, x_5, lean_box(0), x_2, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_4(x_3, x_10, x_13, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_array_size(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_24, x_25, x_23);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_17, 0, x_27);
lean_ctor_set(x_16, 0, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_16);
lean_ctor_set(x_15, 0, x_28);
return x_15;
}
else
{
lean_object* x_29; uint8_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_array_size(x_29);
x_32 = 0;
x_33 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_31, x_32, x_29);
x_34 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_30);
lean_ctor_set(x_16, 0, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_15, 0, x_36);
return x_15;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_40 = x_17;
} else {
 lean_dec_ref(x_17);
 x_40 = lean_box(0);
}
x_41 = lean_array_size(x_38);
x_42 = 0;
x_43 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_41, x_42, x_38);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_40)) {
 x_45 = lean_alloc_ctor(0, 1, 1);
} else {
 x_45 = x_40;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_15, 0, x_47);
return x_15;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_50 = x_16;
} else {
 lean_dec_ref(x_16);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_53 = x_17;
} else {
 lean_dec_ref(x_17);
 x_53 = lean_box(0);
}
x_54 = lean_array_size(x_51);
x_55 = 0;
x_56 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_54, x_55, x_51);
x_57 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_53)) {
 x_58 = lean_alloc_ctor(0, 1, 1);
} else {
 x_58 = x_53;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_52);
if (lean_is_scalar(x_50)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_50;
}
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_49);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_48);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_15);
if (x_62 == 0)
{
return x_15;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_15, 0);
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_15);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_12);
if (x_66 == 0)
{
return x_12;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_12, 0);
x_68 = lean_ctor_get(x_12, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_12);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_9);
if (x_70 == 0)
{
return x_9;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_9, 0);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_9);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4(x_2);
x_13 = l_liftExcept___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__5(x_12, x_7, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_3, x_10, lean_box(0), x_4, x_7, x_15);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_4(x_5, x_14, x_17, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_array_size(x_26);
x_28 = 0;
x_29 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_27, x_28, x_26);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_21, 0, x_30);
lean_ctor_set(x_20, 0, x_4);
x_31 = lean_st_ref_set(x_1, x_20, x_22);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_21);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_array_size(x_36);
x_39 = 0;
x_40 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_38, x_39, x_36);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_37);
lean_ctor_set(x_20, 0, x_4);
x_43 = lean_st_ref_set(x_1, x_20, x_22);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_ctor_get(x_21, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_50 = x_21;
} else {
 lean_dec_ref(x_21);
 x_50 = lean_box(0);
}
x_51 = lean_array_size(x_48);
x_52 = 0;
x_53 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_51, x_52, x_48);
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 1, 1);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_47);
x_57 = lean_st_ref_set(x_1, x_56, x_22);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_16, 0);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_16);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_13);
if (x_69 == 0)
{
return x_13;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_13, 0);
x_71 = lean_ctor_get(x_13, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_13);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__4___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__3___boxed), 8, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
x_11 = l_Lean_Server_RequestM_mapTaskCostly___rarg(x_6, x_10, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___closed__1;
x_15 = l_Task_Priority_default;
x_16 = 1;
lean_inc(x_12);
x_17 = lean_task_map(x_14, x_12, x_15, x_16);
x_18 = lean_st_ref_set(x_7, x_17, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__2___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___boxed), 9, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_4);
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__5(x_5, x_11, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_1, x_5, lean_box(0), x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_4(x_3, x_4, x_9, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(x_2, x_10, lean_box(0), x_3, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_4(x_4, x_5, x_13, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_3);
x_20 = lean_st_ref_set(x_1, x_16, x_17);
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
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_st_ref_set(x_1, x_26, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__8___boxed), 8, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
x_11 = l_Lean_Server_RequestM_mapTaskCostly___rarg(x_6, x_10, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___closed__1;
x_15 = l_Task_Priority_default;
x_16 = 1;
x_17 = lean_task_map(x_14, x_12, x_15, x_16);
x_18 = lean_st_ref_set(x_7, x_17, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__9___boxed), 9, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_6);
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__4___rarg), 5, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Std_Mutex_atomically___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__6(x_5, x_11, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_statefulRequestHandlers;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__1;
x_10 = l_Std_Mutex_new___rarg(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_1);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 0, x_1);
lean_inc(x_10);
x_14 = lean_st_mk_ref(x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__2___boxed), 7, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_4);
lean_inc(x_12);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_15);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6), 8, 5);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_1);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_12);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__7___boxed), 7, 3);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_15);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__10), 8, 5);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_1);
lean_closure_set(x_20, 3, x_5);
lean_closure_set(x_20, 4, x_12);
x_21 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__2;
x_22 = lean_st_ref_take(x_21, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__3;
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set(x_26, 4, x_20);
lean_ctor_set(x_26, 5, x_12);
lean_ctor_set(x_26, 6, x_10);
lean_ctor_set(x_26, 7, x_15);
lean_ctor_set(x_26, 8, x_6);
x_27 = l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(x_23, x_3, x_26);
x_28 = lean_st_ref_set(x_21, x_27, x_24);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
lean_inc(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
lean_inc(x_35);
x_36 = lean_st_mk_ref(x_35, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__2___boxed), 7, 3);
lean_closure_set(x_39, 0, x_3);
lean_closure_set(x_39, 1, x_1);
lean_closure_set(x_39, 2, x_4);
lean_inc(x_33);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_37);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6), 8, 5);
lean_closure_set(x_40, 0, x_37);
lean_closure_set(x_40, 1, x_3);
lean_closure_set(x_40, 2, x_1);
lean_closure_set(x_40, 3, x_4);
lean_closure_set(x_40, 4, x_33);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__7___boxed), 7, 3);
lean_closure_set(x_41, 0, x_3);
lean_closure_set(x_41, 1, x_1);
lean_closure_set(x_41, 2, x_5);
lean_inc(x_33);
lean_inc(x_3);
lean_inc(x_37);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__10), 8, 5);
lean_closure_set(x_42, 0, x_37);
lean_closure_set(x_42, 1, x_3);
lean_closure_set(x_42, 2, x_1);
lean_closure_set(x_42, 3, x_5);
lean_closure_set(x_42, 4, x_33);
x_43 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__2;
x_44 = lean_st_ref_take(x_43, x_38);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__3;
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_42);
lean_ctor_set(x_48, 5, x_33);
lean_ctor_set(x_48, 6, x_35);
lean_ctor_set(x_48, 7, x_37);
lean_ctor_set(x_48, 8, x_6);
x_49 = l_Lean_PersistentHashMap_insert___at___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___spec__7(x_45, x_3, x_48);
x_50 = lean_st_ref_set(x_43, x_49, x_46);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to register stateful LSP request handler for '", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': only possible during initialization", 38, 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_initializing(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1;
x_15 = lean_string_append(x_14, x_1);
lean_dec(x_1);
x_16 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1;
x_21 = lean_string_append(x_20, x_1);
lean_dec(x_1);
x_22 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11(x_4, x_5, x_1, x_6, x_7, x_2, x_27, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3(x_1, x_2, lean_box(0), x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_requestHandlers;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': already registered", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__1;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_12, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_10);
x_15 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3(x_1, x_2, lean_box(0), x_4, x_5, x_6, x_7, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1;
x_17 = lean_string_append(x_16, x_1);
lean_dec(x_1);
x_18 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = l_Lean_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__6(x_21, x_1);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3(x_1, x_2, lean_box(0), x_4, x_5, x_6, x_7, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1;
x_26 = lean_string_append(x_25, x_1);
lean_dec(x_1);
x_27 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
x_11 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2(x_1, x_10, lean_box(0), x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("textDocument/inlayHint", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("workspace/inlayHint/refresh", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleInlayHints), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__1;
x_3 = l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__2;
x_4 = lean_unsigned_to_nat(500u);
x_5 = l_Lean_Server_FileWorker_instTypeNameInlayHintState;
x_6 = l_Lean_Server_FileWorker_InlayHintState_init;
x_7 = l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__3;
x_8 = l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__4;
x_9 = l_Lean_Server_registerPartialStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__1(x_2, x_3, x_4, lean_box(0), x_5, x_6, x_7, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
lean_object* initialize_Lean_Server_GoTo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_InlayHints(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_GoTo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_applyEditToHint_x3f___spec__1___closed__6);
l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__1 = _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__1);
l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__2 = _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__2);
l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__3 = _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__3);
l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__4 = _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__4);
l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__5 = _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737____closed__5);
l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737_ = _init_l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737_();
lean_mark_persistent(l_Lean_Server_FileWorker_instImpl____x40_Lean_Server_FileWorker_InlayHints___hyg_737_);
l_Lean_Server_FileWorker_instTypeNameInlayHintState = _init_l_Lean_Server_FileWorker_instTypeNameInlayHintState();
lean_mark_persistent(l_Lean_Server_FileWorker_instTypeNameInlayHintState);
l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__1 = _init_l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__1);
l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__2 = _init_l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedInlayHintState___closed__2);
l_Lean_Server_FileWorker_instInhabitedInlayHintState = _init_l_Lean_Server_FileWorker_instInhabitedInlayHintState();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedInlayHintState);
l_Lean_Server_FileWorker_InlayHintState_init___closed__1 = _init_l_Lean_Server_FileWorker_InlayHintState_init___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_InlayHintState_init___closed__1);
l_Lean_Server_FileWorker_InlayHintState_init___closed__2 = _init_l_Lean_Server_FileWorker_InlayHintState_init___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_InlayHintState_init___closed__2);
l_Lean_Server_FileWorker_InlayHintState_init = _init_l_Lean_Server_FileWorker_InlayHintState_init();
lean_mark_persistent(l_Lean_Server_FileWorker_InlayHintState_init);
l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__1 = _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__1);
l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__2 = _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__1___closed__2);
l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__1 = _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__1();
lean_mark_persistent(l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__1);
l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__2 = _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__2();
lean_mark_persistent(l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__2);
l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__3 = _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__3();
lean_mark_persistent(l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__3);
l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__4 = _init_l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__4();
lean_mark_persistent(l_panic___at_Lean_Server_FileWorker_handleInlayHints___spec__4___closed__4);
l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__1 = _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__1);
l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__2 = _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__2);
l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__3 = _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__3();
lean_mark_persistent(l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__3);
l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__4 = _init_l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__4();
lean_mark_persistent(l_Lean_Elab_InfoTree_visitM_go___at_Lean_Server_FileWorker_handleInlayHints___spec__3___closed__4);
l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Server_FileWorker_handleInlayHints___spec__6___closed__2);
l_Lean_Server_FileWorker_handleInlayHints___closed__1 = _init_l_Lean_Server_FileWorker_handleInlayHints___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHints___closed__1);
l_Lean_Server_FileWorker_handleInlayHints___closed__2 = _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHints___closed__2);
l_Lean_Server_FileWorker_handleInlayHints___closed__3 = _init_l_Lean_Server_FileWorker_handleInlayHints___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHints___closed__3);
l_Lean_Server_FileWorker_handleInlayHints___closed__4 = _init_l_Lean_Server_FileWorker_handleInlayHints___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHints___closed__4);
l_Lean_Server_FileWorker_handleInlayHints___closed__5 = _init_l_Lean_Server_FileWorker_handleInlayHints___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHints___closed__5);
l_Lean_Server_FileWorker_handleInlayHints___closed__6 = _init_l_Lean_Server_FileWorker_handleInlayHints___closed__6();
l_Lean_Server_FileWorker_handleInlayHints___closed__7 = _init_l_Lean_Server_FileWorker_handleInlayHints___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHints___closed__7);
l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___closed__1 = _init_l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___lambda__2___closed__1);
l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__1 = _init_l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__1);
l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__1 = _init_l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__1();
lean_mark_persistent(l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__1);
l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__2 = _init_l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__2();
lean_mark_persistent(l_Lean_Server_parseRequestParams___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__4___closed__2);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__5___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__6___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__2 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__2();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__2);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__3 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__3();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___lambda__11___closed__3);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__2 = _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__2();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__3___closed__2);
l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__1 = _init_l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__1);
l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__2 = _init_l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__2();
lean_mark_persistent(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____spec__2___closed__2);
l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__1 = _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__1);
l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__2 = _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__2);
l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__3 = _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__3);
l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__4 = _init_l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313____closed__4);
if (builtin) {res = l_Lean_Server_FileWorker_initFn____x40_Lean_Server_FileWorker_InlayHints___hyg_2313_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
