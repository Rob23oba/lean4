// Lean compiler output
// Module: Lean.Data.Lsp.Ipc
// Imports: Init.System.IO Lean.Data.Json Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2484_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_477_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig;
lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForILeansParams____x40_Lean_Data_Lsp_Extra___hyg_687_(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__0(lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Lsp_Ipc_ipcStdioConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 0, 3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 0, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 1, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 2, x_6);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_stream_of_handle(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_stream_of_handle(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdin(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_Stream_writeLspRequest___redArg(x_1, x_6, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_writeRequest___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdin(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_Stream_writeLspNotification___redArg(x_1, x_6, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_writeNotification___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_ctor_set_tag(x_1, 0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
case 5:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_ctor_set_tag(x_1, 1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
x_13 = lean_unsigned_to_nat(80u);
x_14 = l_Lean_Json_pretty(x_1, x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("'", 1, 1);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
x_12 = lean_box(0);
x_6 = x_12;
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
x_6 = x_11;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_6 = x_15;
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_10);
x_11 = lean_box(0);
x_5 = x_11;
goto block_8;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
x_5 = x_10;
goto block_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_5 = x_14;
goto block_8;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_6, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_instInhabitedError;
x_5 = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_panic_fn(x_6, x_1);
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_IO_FS_Stream_readLspMessage(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_12 = x_7;
} else {
 lean_dec_ref(x_7);
 x_12 = lean_box(0);
}
x_13 = l_Lean_Json_isNull(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_14 = lean_mk_string_unchecked("Lean.Data.Lsp.Ipc", 17, 17);
x_15 = lean_mk_string_unchecked("Lean.Lsp.Ipc.shutdown", 21, 21);
x_16 = lean_unsigned_to_nat(51u);
x_17 = lean_unsigned_to_nat(6u);
x_18 = lean_mk_string_unchecked("assertion violation: result.isNull\n      ", 41, 41);
x_19 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_inc(x_4);
x_20 = l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(x_19, x_4, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_5 = x_28;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; uint8_t x_46; 
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_3);
x_34 = l_Lean_JsonNumber_fromNat(x_3);
x_35 = lean_box(0);
x_36 = lean_box(0);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_34);
x_46 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_10, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
goto block_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
lean_dec(x_2);
x_47 = lean_mk_string_unchecked("Expected id ", 12, 12);
x_48 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked(", got id ", 9, 9);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_10, 0);
lean_inc(x_57);
lean_dec(x_10);
x_58 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_58);
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_52 = x_60;
goto block_56;
}
case 1:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
lean_dec(x_10);
x_62 = l_Lean_JsonNumber_toString(x_61);
x_52 = x_62;
goto block_56;
}
default: 
{
lean_object* x_63; 
x_63 = lean_mk_string_unchecked("null", 4, 4);
x_52 = x_63;
goto block_56;
}
}
block_56:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_9)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_9;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_8);
return x_55;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
goto block_44;
}
block_44:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_mk_string_unchecked("exit", 4, 4);
if (lean_is_scalar(x_12)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_12;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(x_2, x_38, x_8);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
return x_39;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_7);
x_64 = lean_ctor_get(x_6, 1);
lean_inc(x_64);
lean_dec(x_6);
x_5 = x_64;
goto _start;
}
}
else
{
uint8_t x_66; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_6);
if (x_66 == 0)
{
return x_6;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_6, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_IO_FS_Stream_readLspMessage(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_12 = x_7;
} else {
 lean_dec_ref(x_7);
 x_12 = lean_box(0);
}
x_13 = l_Lean_Json_isNull(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_14 = lean_mk_string_unchecked("Lean.Data.Lsp.Ipc", 17, 17);
x_15 = lean_mk_string_unchecked("Lean.Lsp.Ipc.shutdown", 21, 21);
x_16 = lean_unsigned_to_nat(51u);
x_17 = lean_unsigned_to_nat(6u);
x_18 = lean_mk_string_unchecked("assertion violation: result.isNull\n      ", 41, 41);
x_19 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_inc(x_4);
x_20 = l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(x_19, x_4, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_45; uint8_t x_46; 
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_3);
x_34 = l_Lean_JsonNumber_fromNat(x_3);
x_35 = lean_box(0);
x_36 = lean_box(0);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_34);
x_46 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_10, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
goto block_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
lean_dec(x_2);
x_47 = lean_mk_string_unchecked("Expected id ", 12, 12);
x_48 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_mk_string_unchecked(", got id ", 9, 9);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_10, 0);
lean_inc(x_57);
lean_dec(x_10);
x_58 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_58);
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_52 = x_60;
goto block_56;
}
case 1:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
lean_dec(x_10);
x_62 = l_Lean_JsonNumber_toString(x_61);
x_52 = x_62;
goto block_56;
}
default: 
{
lean_object* x_63; 
x_63 = lean_mk_string_unchecked("null", 4, 4);
x_52 = x_63;
goto block_56;
}
}
block_56:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_9)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_9;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_8);
return x_55;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
goto block_44;
}
block_44:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_mk_string_unchecked("exit", 4, 4);
if (lean_is_scalar(x_12)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_12;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(x_2, x_38, x_8);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
return x_39;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_7);
x_64 = lean_ctor_get(x_6, 1);
lean_inc(x_64);
lean_dec(x_6);
x_65 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_6);
if (x_66 == 0)
{
return x_6;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_6, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_4 = l_Lean_Lsp_Ipc_stdout(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = l_Lean_Lsp_Ipc_stdin(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = l_Lean_JsonNumber_fromNat(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("shutdown", 8, 8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_inc(x_8);
x_15 = l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0(x_8, x_14, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(x_5, x_8, x_1, x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
return x_17;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Lsp_Ipc_stdout(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_IO_FS_Stream_readLspMessage(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdout(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_Stream_readLspRequestAs___redArg(x_6, x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_readRequestAs___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
x_5 = l_Lean_Lsp_Ipc_stdout(x_3, x_4);
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
x_9 = l_IO_FS_Stream_readLspMessage(x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
switch (lean_obj_tag(x_10)) {
case 2:
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_20, x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_10);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("Expected id ", 12, 12);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_37);
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_24 = x_39;
goto block_35;
}
case 1:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_Lean_JsonNumber_toString(x_40);
x_24 = x_41;
goto block_35;
}
default: 
{
lean_object* x_42; 
x_42 = lean_mk_string_unchecked("null", 4, 4);
x_24 = x_42;
goto block_35;
}
}
block_35:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked(", got id ", 9, 9);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_29);
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_13 = x_27;
x_14 = x_31;
goto block_18;
}
case 1:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = l_Lean_JsonNumber_toString(x_32);
x_13 = x_27;
x_14 = x_33;
goto block_18;
}
default: 
{
lean_object* x_34; 
x_34 = lean_mk_string_unchecked("null", 4, 4);
x_13 = x_27;
x_14 = x_34;
goto block_18;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_20);
lean_dec(x_12);
lean_inc(x_21);
x_43 = lean_apply_1(x_2, x_21);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_free_object(x_10);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
x_47 = l_Lean_Json_compress(x_21);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("'\n", 2, 2);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
x_51 = lean_string_append(x_50, x_45);
lean_dec(x_45);
lean_ctor_set_tag(x_43, 18);
lean_ctor_set(x_43, 0, x_51);
if (lean_is_scalar(x_8)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_8;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_11);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_43, 0);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
x_55 = l_Lean_Json_compress(x_21);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_mk_string_unchecked("'\n", 2, 2);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = lean_string_append(x_58, x_53);
lean_dec(x_53);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_8)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_8;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_11);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_21);
x_62 = lean_ctor_get(x_43, 0);
lean_inc(x_62);
lean_dec(x_43);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_62);
lean_ctor_set(x_10, 0, x_1);
if (lean_is_scalar(x_8)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_8;
}
lean_ctor_set(x_63, 0, x_10);
lean_ctor_set(x_63, 1, x_11);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_64, x_1);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_2);
x_67 = lean_mk_string_unchecked("Expected id ", 12, 12);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_81);
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_68 = x_83;
goto block_79;
}
case 1:
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
lean_dec(x_1);
x_85 = l_Lean_JsonNumber_toString(x_84);
x_68 = x_85;
goto block_79;
}
default: 
{
lean_object* x_86; 
x_86 = lean_mk_string_unchecked("null", 4, 4);
x_68 = x_86;
goto block_79;
}
}
block_79:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_string_append(x_67, x_68);
lean_dec(x_68);
x_70 = lean_mk_string_unchecked(", got id ", 9, 9);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
switch (lean_obj_tag(x_64)) {
case 0:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_73);
x_74 = lean_string_append(x_73, x_72);
lean_dec(x_72);
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_13 = x_71;
x_14 = x_75;
goto block_18;
}
case 1:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_64, 0);
lean_inc(x_76);
lean_dec(x_64);
x_77 = l_Lean_JsonNumber_toString(x_76);
x_13 = x_71;
x_14 = x_77;
goto block_18;
}
default: 
{
lean_object* x_78; 
x_78 = lean_mk_string_unchecked("null", 4, 4);
x_13 = x_71;
x_14 = x_78;
goto block_18;
}
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_64);
lean_dec(x_12);
lean_inc(x_65);
x_87 = lean_apply_1(x_2, x_65);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
x_91 = l_Lean_Json_compress(x_65);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_93 = lean_mk_string_unchecked("'\n", 2, 2);
x_94 = lean_string_append(x_92, x_93);
lean_dec(x_93);
x_95 = lean_string_append(x_94, x_88);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_96 = lean_alloc_ctor(18, 1, 0);
} else {
 x_96 = x_89;
 lean_ctor_set_tag(x_96, 18);
}
lean_ctor_set(x_96, 0, x_95);
if (lean_is_scalar(x_8)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_8;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_11);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_65);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_8)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_8;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_11);
return x_100;
}
}
}
}
case 3:
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_138; lean_object* x_139; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_10, 0);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_103 = lean_ctor_get(x_10, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_10, 2);
lean_inc(x_104);
lean_dec(x_10);
x_105 = lean_mk_string_unchecked("Expected JSON-RPC response, got: '", 34, 34);
x_106 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_107 = lean_mk_string_unchecked("2.0", 3, 3);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_138 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_101)) {
case 0:
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_101);
if (x_204 == 0)
{
lean_ctor_set_tag(x_101, 3);
x_139 = x_101;
goto block_203;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_101, 0);
lean_inc(x_205);
lean_dec(x_101);
x_206 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_139 = x_206;
goto block_203;
}
}
case 1:
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_101);
if (x_207 == 0)
{
lean_ctor_set_tag(x_101, 2);
x_139 = x_101;
goto block_203;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_101, 0);
lean_inc(x_208);
lean_dec(x_101);
x_209 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_209, 0, x_208);
x_139 = x_209;
goto block_203;
}
}
default: 
{
lean_object* x_210; 
x_210 = lean_box(0);
x_139 = x_210;
goto block_203;
}
}
block_137:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked("message", 7, 7);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_103);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_121, 0, lean_box(0));
x_122 = lean_mk_string_unchecked("data", 4, 4);
x_123 = l_Lean_Json_opt___redArg(x_121, x_122, x_104);
x_124 = l_List_appendTR(lean_box(0), x_120, x_123);
x_125 = l_Lean_Json_mkObj(x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_110);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_118);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_111);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_109);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Json_mkObj(x_129);
x_131 = l_Lean_Json_compress(x_130);
x_132 = lean_string_append(x_105, x_131);
lean_dec(x_131);
x_133 = lean_mk_string_unchecked("'", 1, 1);
x_134 = lean_string_append(x_132, x_133);
lean_dec(x_133);
x_135 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_135, 0, x_134);
if (lean_is_scalar(x_8)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_8;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_11);
return x_136;
}
block_203:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_mk_string_unchecked("error", 5, 5);
x_142 = lean_mk_string_unchecked("code", 4, 4);
switch (x_102) {
case 0:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_unsigned_to_nat(32700u);
x_144 = lean_nat_to_int(x_143);
x_145 = lean_int_neg(x_144);
lean_dec(x_144);
x_146 = l_Lean_JsonNumber_fromInt(x_145);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_147;
goto block_137;
}
case 1:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_unsigned_to_nat(32600u);
x_149 = lean_nat_to_int(x_148);
x_150 = lean_int_neg(x_149);
lean_dec(x_149);
x_151 = l_Lean_JsonNumber_fromInt(x_150);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_152;
goto block_137;
}
case 2:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_unsigned_to_nat(32601u);
x_154 = lean_nat_to_int(x_153);
x_155 = lean_int_neg(x_154);
lean_dec(x_154);
x_156 = l_Lean_JsonNumber_fromInt(x_155);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_157;
goto block_137;
}
case 3:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_unsigned_to_nat(32602u);
x_159 = lean_nat_to_int(x_158);
x_160 = lean_int_neg(x_159);
lean_dec(x_159);
x_161 = l_Lean_JsonNumber_fromInt(x_160);
x_162 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_162;
goto block_137;
}
case 4:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_unsigned_to_nat(32603u);
x_164 = lean_nat_to_int(x_163);
x_165 = lean_int_neg(x_164);
lean_dec(x_164);
x_166 = l_Lean_JsonNumber_fromInt(x_165);
x_167 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_167;
goto block_137;
}
case 5:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_unsigned_to_nat(32002u);
x_169 = lean_nat_to_int(x_168);
x_170 = lean_int_neg(x_169);
lean_dec(x_169);
x_171 = l_Lean_JsonNumber_fromInt(x_170);
x_172 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_172;
goto block_137;
}
case 6:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_unsigned_to_nat(32001u);
x_174 = lean_nat_to_int(x_173);
x_175 = lean_int_neg(x_174);
lean_dec(x_174);
x_176 = l_Lean_JsonNumber_fromInt(x_175);
x_177 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_177;
goto block_137;
}
case 7:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = lean_unsigned_to_nat(32801u);
x_179 = lean_nat_to_int(x_178);
x_180 = lean_int_neg(x_179);
lean_dec(x_179);
x_181 = l_Lean_JsonNumber_fromInt(x_180);
x_182 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_182;
goto block_137;
}
case 8:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_unsigned_to_nat(32800u);
x_184 = lean_nat_to_int(x_183);
x_185 = lean_int_neg(x_184);
lean_dec(x_184);
x_186 = l_Lean_JsonNumber_fromInt(x_185);
x_187 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_187;
goto block_137;
}
case 9:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_188 = lean_unsigned_to_nat(32900u);
x_189 = lean_nat_to_int(x_188);
x_190 = lean_int_neg(x_189);
lean_dec(x_189);
x_191 = l_Lean_JsonNumber_fromInt(x_190);
x_192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_192;
goto block_137;
}
case 10:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_unsigned_to_nat(32901u);
x_194 = lean_nat_to_int(x_193);
x_195 = lean_int_neg(x_194);
lean_dec(x_194);
x_196 = l_Lean_JsonNumber_fromInt(x_195);
x_197 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_197;
goto block_137;
}
default: 
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_unsigned_to_nat(32902u);
x_199 = lean_nat_to_int(x_198);
x_200 = lean_int_neg(x_199);
lean_dec(x_199);
x_201 = l_Lean_JsonNumber_fromInt(x_200);
x_202 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_110 = x_141;
x_111 = x_140;
x_112 = x_142;
x_113 = x_202;
goto block_137;
}
}
}
}
default: 
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
if (lean_is_scalar(x_12)) {
 x_17 = lean_alloc_ctor(1, 2, 0);
} else {
 x_17 = x_12;
 lean_ctor_set_tag(x_17, 1);
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
uint8_t x_212; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_9);
if (x_212 == 0)
{
return x_9;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_9, 0);
x_214 = lean_ctor_get(x_9, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_9);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_readResponseAs___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_4 = lean_io_process_child_wait(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_Ipc_waitForExit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_Lsp_Ipc_readMessage(x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
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
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_dec(x_12);
lean_dec(x_10);
x_3 = x_11;
goto _start;
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_dec(x_10);
x_41 = lean_mk_string_unchecked("textDocument/publishDiagnostics", 31, 31);
x_42 = lean_string_dec_eq(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_12);
x_3 = x_11;
goto _start;
}
else
{
if (lean_obj_tag(x_40) == 0)
{
lean_dec(x_12);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_ctor_set_tag(x_45, 4);
x_13 = x_45;
goto block_37;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_13 = x_48;
goto block_37;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_ctor_set_tag(x_45, 5);
x_13 = x_45;
goto block_37;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_13 = x_51;
goto block_37;
}
}
}
}
}
case 2:
{
uint8_t x_52; 
lean_dec(x_12);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_10, 0);
x_54 = lean_ctor_get(x_10, 1);
lean_dec(x_54);
x_55 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_53, x_1);
lean_dec(x_53);
if (x_55 == 0)
{
lean_free_object(x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_57; 
lean_dec(x_2);
x_57 = lean_box(0);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_11);
lean_ctor_set(x_10, 0, x_57);
return x_10;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_10, 0);
lean_inc(x_58);
lean_dec(x_10);
x_59 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_58, x_1);
lean_dec(x_58);
if (x_59 == 0)
{
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_11);
return x_62;
}
}
}
default: 
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_12);
x_63 = lean_ctor_get(x_10, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_10, 1);
lean_inc(x_64);
lean_dec(x_10);
x_65 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_63, x_1);
lean_dec(x_63);
if (x_65 == 0)
{
lean_dec(x_64);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_2);
x_67 = lean_mk_string_unchecked("Waiting for diagnostics failed: ", 32, 32);
x_68 = lean_string_append(x_67, x_64);
lean_dec(x_64);
x_69 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_11);
return x_70;
}
}
}
block_37:
{
lean_object* x_14; 
x_14 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2484_(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_mk_string_unchecked("Cannot decode publishDiagnostics parameters\n", 44, 44);
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 18);
lean_ctor_set(x_14, 0, x_18);
if (lean_is_scalar(x_12)) {
 x_19 = lean_alloc_ctor(1, 2, 0);
} else {
 x_19 = x_12;
 lean_ctor_set_tag(x_19, 1);
}
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_mk_string_unchecked("Cannot decode publishDiagnostics parameters\n", 44, 44);
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
if (lean_is_scalar(x_12)) {
 x_24 = lean_alloc_ctor(1, 2, 0);
} else {
 x_24 = x_12;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_mk_string_unchecked("textDocument/publishDiagnostics", 31, 31);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 0, x_31);
x_4 = x_29;
x_5 = x_26;
goto block_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_mk_string_unchecked("textDocument/publishDiagnostics", 31, 31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
x_4 = x_32;
x_5 = x_34;
goto block_8;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_4 = x_35;
x_5 = x_36;
goto block_8;
}
}
else
{
lean_dec(x_25);
return x_26;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_9);
if (x_71 == 0)
{
return x_9;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_9, 0);
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_9);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_477_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__0(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
x_12 = lean_box(0);
x_6 = x_12;
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
x_6 = x_11;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_6 = x_15;
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Lsp_Ipc_stdin(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(x_5, x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_mk_string_unchecked("textDocument/waitForDiagnostics", 31, 31);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_inc(x_4);
x_9 = l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_4, x_10);
lean_dec(x_1);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForILeansParams____x40_Lean_Data_Lsp_Extra___hyg_687_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__0(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
x_12 = lean_box(0);
x_6 = x_12;
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
x_6 = x_11;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_6 = x_15;
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Lsp_Ipc_stdin(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(x_5, x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Lsp_Ipc_readMessage(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 2:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
x_12 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_10, x_1);
lean_dec(x_10);
if (x_12 == 0)
{
lean_free_object(x_5);
lean_free_object(x_4);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_4;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_free_object(x_4);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_23, x_1);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_24);
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_24)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_24;
 lean_ctor_set_tag(x_29, 0);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
case 3:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_4, 1);
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_34, x_1);
lean_dec(x_34);
if (x_36 == 0)
{
lean_dec(x_35);
lean_free_object(x_4);
x_3 = x_32;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_38 = lean_mk_string_unchecked("Waiting for ILeans failed: ", 27, 27);
x_39 = lean_string_append(x_38, x_35);
lean_dec(x_35);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_40);
return x_4;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_ctor_get(x_5, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
x_44 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_42, x_1);
lean_dec(x_42);
if (x_44 == 0)
{
lean_dec(x_43);
x_3 = x_41;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_46 = lean_mk_string_unchecked("Waiting for ILeans failed: ", 27, 27);
x_47 = lean_string_append(x_46, x_43);
lean_dec(x_43);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
default: 
{
lean_object* x_50; 
lean_dec(x_5);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_dec(x_4);
x_3 = x_50;
goto _start;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_4);
if (x_52 == 0)
{
return x_4;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_4, 0);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_mk_string_unchecked("$/lean/waitForILeans", 20, 20);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_inc(x_4);
x_9 = l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(x_1, x_4, x_10);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
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
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 6);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_dec_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Lsp_Ipc_readMessage(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_mk_string_unchecked("textDocument/publishDiagnostics", 31, 31);
x_37 = lean_string_dec_eq(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
else
{
if (lean_obj_tag(x_35) == 0)
{
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 4);
x_8 = x_40;
goto block_33;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_8 = x_43;
goto block_33;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_ctor_set_tag(x_40, 5);
x_8 = x_40;
goto block_33;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_8 = x_46;
goto block_33;
}
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
x_3 = x_6;
goto _start;
}
block_33:
{
lean_object* x_9; 
x_9 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2484_(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_mk_string_unchecked("Cannot decode publishDiagnostics parameters\n", 44, 44);
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
lean_ctor_set_tag(x_9, 18);
lean_ctor_set(x_9, 0, x_13);
if (lean_is_scalar(x_7)) {
 x_14 = lean_alloc_ctor(1, 2, 0);
} else {
 x_14 = x_7;
 lean_ctor_set_tag(x_14, 1);
}
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_mk_string_unchecked("Cannot decode publishDiagnostics parameters\n", 44, 44);
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
if (lean_is_scalar(x_7)) {
 x_19 = lean_alloc_ctor(1, 2, 0);
} else {
 x_19 = x_7;
 lean_ctor_set_tag(x_19, 1);
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
else
{
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_usize_of_nat(x_22);
x_28 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_29 = l_Array_anyMUnsafe_any___at___Lean_Lsp_Ipc_waitForMessage_loop_spec__0(x_1, x_21, x_27, x_28);
lean_dec(x_21);
if (x_29 == 0)
{
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_31 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_7;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
}
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_4);
if (x_48 == 0)
{
return x_4;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_4);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Lsp_Ipc_waitForMessage_loop_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Ipc_waitForMessage_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Ipc_waitForMessage_loop(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Ipc_waitForMessage(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_5 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_8);
x_12 = lean_unbox(x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_12);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_13);
x_14 = lean_io_process_spawn(x_11, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_2(x_3, x_15, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_runWith___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Ipc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_Ipc_ipcStdioConfig = _init_l_Lean_Lsp_Ipc_ipcStdioConfig();
lean_mark_persistent(l_Lean_Lsp_Ipc_ipcStdioConfig);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
