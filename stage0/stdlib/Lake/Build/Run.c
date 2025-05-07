// Lean compiler output
// Module: Lake.Build.Run
// Imports: Lake.Util.Lock Lake.Build.Index Lake.Build.Job
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonitorM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_instOrdLogLevel;
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_Ansi_chalk(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_recFetchWithIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_flush(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_print_x21(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobAction_verb(uint8_t, uint8_t);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_print_x21___lam__0___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_spinnerFrames;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_main___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LogLevel_ansiColor(uint8_t);
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Monitor_main___lam__0(uint8_t, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Job_Basic_0__Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
lean_object* l_Lake_OptDataKind_anonymous(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Ansi_resetLine;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint32_t l_Lake_LogLevel_icon(uint8_t);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_poll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_print_x21___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_versionStringCore;
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_poll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_flush(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Monitor_main(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkBuildContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_5);
x_6 = lean_st_mk_ref(x_5, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lake_Env_leanGithash(x_9);
lean_dec(x_9);
x_11 = lean_string_hash(x_10);
x_12 = l_Lake_Hash_nil;
x_13 = lean_uint64_mix_hash(x_12, x_11);
x_14 = lean_mk_string_unchecked("Lean ", 5, 5);
x_15 = l_Lean_versionStringCore;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_mk_string_unchecked(", commit ", 9, 9);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_10);
lean_dec(x_10);
x_20 = lean_nat_to_int(x_4);
x_21 = lean_uint32_of_nat(x_4);
x_22 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint32(x_22, sizeof(void*)*1, x_21);
x_23 = lean_box_uint64(x_13);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_1);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_8);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint32_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = l_Lake_Env_leanGithash(x_28);
lean_dec(x_28);
x_30 = lean_string_hash(x_29);
x_31 = l_Lake_Hash_nil;
x_32 = lean_uint64_mix_hash(x_31, x_30);
x_33 = lean_mk_string_unchecked("Lean ", 5, 5);
x_34 = l_Lean_versionStringCore;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_mk_string_unchecked(", commit ", 9, 9);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_37, x_29);
lean_dec(x_29);
x_39 = lean_nat_to_int(x_4);
x_40 = lean_uint32_of_nat(x_4);
x_41 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint32(x_41, sizeof(void*)*1, x_40);
x_42 = lean_box_uint64(x_32);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_5);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_1);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_26);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_27);
return x_45;
}
}
}
static lean_object* _init_l_Lake_Monitor_spinnerFrames() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_unsigned_to_nat(10494u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_unsigned_to_nat(10487u);
x_4 = l_Char_ofNat(x_3);
x_5 = lean_unsigned_to_nat(10479u);
x_6 = l_Char_ofNat(x_5);
x_7 = lean_unsigned_to_nat(10463u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_unsigned_to_nat(10367u);
x_10 = l_Char_ofNat(x_9);
x_11 = lean_unsigned_to_nat(10431u);
x_12 = l_Char_ofNat(x_11);
x_13 = lean_unsigned_to_nat(10491u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_unsigned_to_nat(10493u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_unsigned_to_nat(8u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_box_uint32(x_2);
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_box_uint32(x_4);
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_box_uint32(x_6);
x_24 = lean_array_push(x_22, x_23);
x_25 = lean_box_uint32(x_8);
x_26 = lean_array_push(x_24, x_25);
x_27 = lean_box_uint32(x_10);
x_28 = lean_array_push(x_26, x_27);
x_29 = lean_box_uint32(x_12);
x_30 = lean_array_push(x_28, x_29);
x_31 = lean_box_uint32(x_14);
x_32 = lean_array_push(x_30, x_31);
x_33 = lean_box_uint32(x_16);
x_34 = lean_array_push(x_32, x_33);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_3, x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_MonitorM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_4, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Ansi_resetLine() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\x1b[2K\r", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_flush(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_print_x21___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_print_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_instMonadEIO(lean_box(0));
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_apply_2(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_2);
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
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
x_15 = l_instInhabitedOfMonad___redArg(x_4, x_13);
x_16 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_17 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_18 = lean_unsigned_to_nat(79u);
x_19 = lean_unsigned_to_nat(4u);
x_20 = lean_mk_string_unchecked("[", 1, 1);
x_21 = lean_mk_string_unchecked("Lake", 4, 4);
x_22 = lean_mk_string_unchecked("print!", 6, 6);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Name_toString(x_23, x_25, x_14);
x_27 = lean_string_append(x_20, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_io_error_to_string(x_11);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("] ", 2, 2);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_String_quote(x_2);
lean_dec(x_2);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unsigned_to_nat(120u);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_format_pretty(x_35, x_36, x_37, x_37);
x_39 = lean_string_append(x_33, x_38);
lean_dec(x_38);
x_40 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_16, x_17, x_18, x_19, x_39);
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_16);
x_41 = l_panic___redArg(x_15, x_40);
x_42 = lean_apply_1(x_41, x_12);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lake_print_x21___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_print_x21___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_print(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_instMonadEIO(lean_box(0));
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_apply_2(x_12, x_1, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_5 = x_14;
x_6 = x_15;
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
x_20 = l_instInhabitedOfMonad___redArg(x_11, x_18);
x_21 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_22 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_23 = lean_unsigned_to_nat(79u);
x_24 = lean_unsigned_to_nat(4u);
x_25 = lean_mk_string_unchecked("[", 1, 1);
x_26 = lean_mk_string_unchecked("Lake", 4, 4);
x_27 = lean_mk_string_unchecked("print!", 6, 6);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Name_toString(x_28, x_30, x_19);
x_32 = lean_string_append(x_25, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_io_error_to_string(x_16);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_mk_string_unchecked("] ", 2, 2);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = l_String_quote(x_1);
lean_dec(x_1);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_unsigned_to_nat(120u);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_format_pretty(x_40, x_41, x_42, x_42);
x_44 = lean_string_append(x_38, x_43);
lean_dec(x_43);
x_45 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_21, x_22, x_23, x_24, x_44);
lean_dec(x_44);
lean_dec(x_22);
lean_dec(x_21);
x_46 = l_panic___redArg(x_20, x_45);
x_47 = lean_apply_1(x_46, x_17);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_5 = x_48;
x_6 = x_49;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_flush(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_1(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_4 = x_12;
x_5 = x_13;
goto block_8;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_4 = x_15;
x_5 = x_14;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 5);
if (x_10 == 0)
{
lean_dec(x_3);
goto block_9;
}
else
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 4);
if (x_11 == 0)
{
lean_dec(x_3);
goto block_9;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_31; lean_object* x_39; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
x_19 = l_Lake_Monitor_spinnerFrames;
x_20 = lean_array_get_size(x_19);
x_21 = lean_array_fget(x_19, x_16);
x_22 = lean_unbox_uint32(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Fin_add(x_20, x_16, x_23);
lean_dec(x_16);
lean_dec(x_20);
x_25 = lean_mk_string_unchecked("\x1b[2K\r", 5, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_ctor_set(x_4, 5, x_24);
lean_ctor_set(x_4, 3, x_25);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_1);
x_86 = lean_nat_dec_lt(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_85);
x_87 = lean_mk_string_unchecked("Running ", 8, 8);
x_88 = lean_array_get_size(x_2);
x_89 = lean_nat_sub(x_88, x_23);
lean_dec(x_88);
x_90 = lean_array_fget(x_2, x_89);
lean_dec(x_89);
x_91 = lean_ctor_get(x_90, 2);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_string_append(x_87, x_91);
lean_dec(x_91);
x_39 = x_92;
goto block_83;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_mk_string_unchecked("Running ", 8, 8);
x_94 = lean_nat_sub(x_85, x_23);
lean_dec(x_85);
x_95 = lean_array_fget(x_1, x_94);
x_96 = lean_ctor_get(x_95, 2);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_string_append(x_93, x_96);
lean_dec(x_96);
x_98 = lean_mk_string_unchecked(" (+ ", 4, 4);
x_99 = lean_string_append(x_97, x_98);
lean_dec(x_98);
x_100 = l___private_Init_Data_Repr_0__Nat_reprFast(x_94);
x_101 = lean_string_append(x_99, x_100);
lean_dec(x_100);
x_102 = lean_mk_string_unchecked(" more)", 6, 6);
x_103 = lean_string_append(x_101, x_102);
lean_dec(x_102);
x_39 = x_103;
goto block_83;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
block_38:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_apply_1(x_32, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_26 = x_34;
x_27 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_26 = x_37;
x_27 = x_36;
goto block_30;
}
}
block_83:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = lean_string_push(x_40, x_22);
x_42 = lean_string_append(x_15, x_41);
lean_dec(x_41);
x_43 = lean_mk_string_unchecked(" [", 2, 2);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = lean_mk_string_unchecked("/", 1, 1);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("] ", 2, 2);
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_39);
lean_dec(x_39);
x_54 = lean_ctor_get(x_17, 4);
lean_inc(x_54);
lean_inc(x_53);
x_55 = lean_apply_2(x_54, x_53, x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_18);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_31 = x_56;
goto block_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_60 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_61 = lean_unsigned_to_nat(79u);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_mk_string_unchecked("[", 1, 1);
x_64 = lean_mk_string_unchecked("Lake", 4, 4);
x_65 = lean_mk_string_unchecked("print!", 6, 6);
x_66 = l_Lean_Name_mkStr2(x_64, x_65);
x_67 = l_Lean_Name_toString(x_66, x_11, x_18);
x_68 = lean_string_append(x_63, x_67);
lean_dec(x_67);
x_69 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = lean_io_error_to_string(x_57);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_73 = lean_string_append(x_72, x_51);
lean_dec(x_51);
x_74 = l_String_quote(x_53);
lean_dec(x_53);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_unsigned_to_nat(120u);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_format_pretty(x_75, x_76, x_77, x_77);
x_79 = lean_string_append(x_73, x_78);
lean_dec(x_78);
x_80 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_59, x_60, x_61, x_62, x_79);
lean_dec(x_79);
lean_dec(x_60);
lean_dec(x_59);
x_81 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_80, x_58);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_31 = x_82;
goto block_38;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint32_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_125; lean_object* x_133; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_104 = lean_ctor_get(x_4, 0);
x_105 = lean_ctor_get(x_4, 1);
x_106 = lean_ctor_get(x_4, 2);
x_107 = lean_ctor_get(x_4, 3);
x_108 = lean_ctor_get(x_4, 4);
x_109 = lean_ctor_get(x_4, 5);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_4);
x_110 = lean_ctor_get(x_3, 1);
lean_inc(x_110);
lean_dec(x_3);
x_111 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
x_112 = l_Lake_Monitor_spinnerFrames;
x_113 = lean_array_get_size(x_112);
x_114 = lean_array_fget(x_112, x_109);
x_115 = lean_unbox_uint32(x_114);
lean_dec(x_114);
x_116 = lean_unsigned_to_nat(1u);
x_117 = l_Fin_add(x_113, x_109, x_116);
lean_dec(x_109);
lean_dec(x_113);
x_118 = lean_mk_string_unchecked("\x1b[2K\r", 5, 5);
lean_inc(x_105);
lean_inc(x_104);
x_119 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_119, 0, x_104);
lean_ctor_set(x_119, 1, x_105);
lean_ctor_set(x_119, 2, x_106);
lean_ctor_set(x_119, 3, x_118);
lean_ctor_set(x_119, 4, x_108);
lean_ctor_set(x_119, 5, x_117);
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_array_get_size(x_1);
x_180 = lean_nat_dec_lt(x_178, x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_179);
x_181 = lean_mk_string_unchecked("Running ", 8, 8);
x_182 = lean_array_get_size(x_2);
x_183 = lean_nat_sub(x_182, x_116);
lean_dec(x_182);
x_184 = lean_array_fget(x_2, x_183);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_string_append(x_181, x_185);
lean_dec(x_185);
x_133 = x_186;
goto block_177;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_187 = lean_mk_string_unchecked("Running ", 8, 8);
x_188 = lean_nat_sub(x_179, x_116);
lean_dec(x_179);
x_189 = lean_array_fget(x_1, x_188);
x_190 = lean_ctor_get(x_189, 2);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_string_append(x_187, x_190);
lean_dec(x_190);
x_192 = lean_mk_string_unchecked(" (+ ", 4, 4);
x_193 = lean_string_append(x_191, x_192);
lean_dec(x_192);
x_194 = l___private_Init_Data_Repr_0__Nat_reprFast(x_188);
x_195 = lean_string_append(x_193, x_194);
lean_dec(x_194);
x_196 = lean_mk_string_unchecked(" more)", 6, 6);
x_197 = lean_string_append(x_195, x_196);
lean_dec(x_196);
x_133 = x_197;
goto block_177;
}
block_124:
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
block_132:
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_110, 0);
lean_inc(x_126);
lean_dec(x_110);
x_127 = lean_apply_1(x_126, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_120 = x_128;
x_121 = x_129;
goto block_124;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_box(0);
x_120 = x_131;
x_121 = x_130;
goto block_124;
}
}
block_177:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = lean_string_push(x_134, x_115);
x_136 = lean_string_append(x_107, x_135);
lean_dec(x_135);
x_137 = lean_mk_string_unchecked(" [", 2, 2);
x_138 = lean_string_append(x_136, x_137);
lean_dec(x_137);
x_139 = l___private_Init_Data_Repr_0__Nat_reprFast(x_104);
x_140 = lean_string_append(x_138, x_139);
lean_dec(x_139);
x_141 = lean_mk_string_unchecked("/", 1, 1);
x_142 = lean_string_append(x_140, x_141);
lean_dec(x_141);
x_143 = l___private_Init_Data_Repr_0__Nat_reprFast(x_105);
x_144 = lean_string_append(x_142, x_143);
lean_dec(x_143);
x_145 = lean_mk_string_unchecked("] ", 2, 2);
x_146 = lean_string_append(x_144, x_145);
x_147 = lean_string_append(x_146, x_133);
lean_dec(x_133);
x_148 = lean_ctor_get(x_110, 4);
lean_inc(x_148);
lean_inc(x_147);
x_149 = lean_apply_2(x_148, x_147, x_5);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_111);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_125 = x_150;
goto block_132;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_154 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_155 = lean_unsigned_to_nat(79u);
x_156 = lean_unsigned_to_nat(4u);
x_157 = lean_mk_string_unchecked("[", 1, 1);
x_158 = lean_mk_string_unchecked("Lake", 4, 4);
x_159 = lean_mk_string_unchecked("print!", 6, 6);
x_160 = l_Lean_Name_mkStr2(x_158, x_159);
x_161 = l_Lean_Name_toString(x_160, x_11, x_111);
x_162 = lean_string_append(x_157, x_161);
lean_dec(x_161);
x_163 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_164 = lean_string_append(x_162, x_163);
lean_dec(x_163);
x_165 = lean_io_error_to_string(x_151);
x_166 = lean_string_append(x_164, x_165);
lean_dec(x_165);
x_167 = lean_string_append(x_166, x_145);
lean_dec(x_145);
x_168 = l_String_quote(x_147);
lean_dec(x_147);
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_unsigned_to_nat(120u);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_format_pretty(x_169, x_170, x_171, x_171);
x_173 = lean_string_append(x_167, x_172);
lean_dec(x_172);
x_174 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_153, x_154, x_155, x_156, x_173);
lean_dec(x_173);
lean_dec(x_154);
lean_dec(x_153);
x_175 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_174, x_152);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_125 = x_176;
goto block_132;
}
}
}
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Monitor_renderProgress___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Monitor_renderProgress___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_renderProgress___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_Monitor_renderProgress(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_5, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_7);
x_11 = lean_array_uget(x_4, x_5);
lean_inc(x_1);
x_12 = l_Lake_logToStream(x_11, x_1, x_2, x_3, x_9);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_7 = x_13;
x_9 = x_14;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_reportJob(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; uint32_t x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; uint32_t x_174; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; uint8_t x_185; uint8_t x_186; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; uint8_t x_211; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; lean_object* x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; lean_object* x_251; uint8_t x_252; uint8_t x_253; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_261; uint8_t x_262; uint8_t x_263; lean_object* x_264; uint8_t x_265; uint8_t x_266; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; lean_object* x_279; uint8_t x_280; uint8_t x_281; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; lean_object* x_293; uint8_t x_294; uint8_t x_295; uint8_t x_296; lean_object* x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; uint8_t x_316; uint8_t x_317; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_352; lean_object* x_353; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 2);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 3);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 4);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 5);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_70 = lean_alloc_closure((void*)(l_Lake_print_x21___lam__0___boxed), 1, 0);
x_201 = lean_box(1);
x_202 = lean_box(0);
x_330 = lean_alloc_closure((void*)(l___private_Lake_Build_Job_Basic_0__Lake_ordJobAction____x40_Lake_Build_Job_Basic___hyg_268____boxed), 2, 0);
x_331 = l_Lake_instOrdLogLevel;
x_352 = lean_task_get_own(x_67);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
x_332 = x_353;
goto block_351;
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_27:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_1(x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_11 = x_18;
x_12 = x_23;
x_13 = x_24;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_11 = x_18;
x_12 = x_26;
x_13 = x_25;
goto block_16;
}
}
block_57:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_41);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_34);
x_17 = x_44;
x_18 = x_43;
x_19 = x_42;
goto block_27;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_34);
x_17 = x_44;
x_18 = x_43;
x_19 = x_42;
goto block_27;
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_box(0);
x_51 = lean_usize_of_nat(x_46);
x_52 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_53 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_34, x_45, x_39, x_41, x_51, x_52, x_50, x_43, x_42);
lean_dec(x_41);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_17 = x_44;
x_18 = x_56;
x_19 = x_55;
goto block_27;
}
}
}
block_66:
{
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_34);
x_17 = x_62;
x_18 = x_61;
x_19 = x_63;
goto block_27;
}
else
{
if (x_58 == 0)
{
x_41 = x_59;
x_42 = x_63;
x_43 = x_61;
x_44 = x_62;
x_45 = x_35;
goto block_57;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_box(0);
x_65 = lean_unbox(x_64);
x_41 = x_59;
x_42 = x_63;
x_43 = x_61;
x_44 = x_62;
x_45 = x_65;
goto block_57;
}
}
}
block_122:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_74, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_74, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_74, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 5);
lean_inc(x_84);
lean_dec(x_74);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_76);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set(x_85, 5, x_84);
x_86 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_87 = lean_mk_string_unchecked("\n", 1, 1);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = lean_ctor_get(x_77, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 4);
lean_inc(x_90);
lean_dec(x_89);
lean_inc(x_88);
x_91 = lean_apply_2(x_90, x_88, x_71);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_dec(x_88);
lean_dec(x_70);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_58 = x_73;
x_59 = x_72;
x_60 = x_75;
x_61 = x_85;
x_62 = x_77;
x_63 = x_92;
goto block_66;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_96 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_97 = lean_unsigned_to_nat(79u);
x_98 = lean_unsigned_to_nat(4u);
x_99 = lean_mk_string_unchecked("[", 1, 1);
x_100 = lean_mk_string_unchecked("Lake", 4, 4);
x_101 = lean_mk_string_unchecked("print!", 6, 6);
x_102 = l_Lean_Name_mkStr2(x_100, x_101);
x_103 = lean_box(1);
x_104 = lean_unbox(x_103);
x_105 = l_Lean_Name_toString(x_102, x_104, x_70);
x_106 = lean_string_append(x_99, x_105);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = lean_io_error_to_string(x_93);
x_110 = lean_string_append(x_108, x_109);
lean_dec(x_109);
x_111 = lean_mk_string_unchecked("] ", 2, 2);
x_112 = lean_string_append(x_110, x_111);
lean_dec(x_111);
x_113 = l_String_quote(x_88);
lean_dec(x_88);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_unsigned_to_nat(120u);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_format_pretty(x_114, x_115, x_116, x_116);
x_118 = lean_string_append(x_112, x_117);
lean_dec(x_117);
x_119 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_95, x_96, x_97, x_98, x_118);
lean_dec(x_118);
lean_dec(x_96);
lean_dec(x_95);
x_120 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_119, x_94);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_58 = x_73;
x_59 = x_72;
x_60 = x_75;
x_61 = x_85;
x_62 = x_77;
x_63 = x_121;
goto block_66;
}
}
block_133:
{
lean_object* x_132; 
x_132 = l_Lake_Ansi_chalk(x_131, x_126);
lean_dec(x_126);
lean_dec(x_131);
x_71 = x_123;
x_72 = x_125;
x_73 = x_124;
x_74 = x_127;
x_75 = x_128;
x_76 = x_129;
x_77 = x_130;
x_78 = x_132;
goto block_122;
}
block_164:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_144 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_144);
x_145 = lean_string_push(x_144, x_140);
x_146 = lean_mk_string_unchecked(" [", 2, 2);
x_147 = lean_string_append(x_145, x_146);
lean_dec(x_146);
x_148 = l___private_Init_Data_Repr_0__Nat_reprFast(x_28);
x_149 = lean_string_append(x_147, x_148);
lean_dec(x_148);
x_150 = lean_mk_string_unchecked("/", 1, 1);
x_151 = lean_string_append(x_149, x_150);
lean_dec(x_150);
x_152 = l___private_Init_Data_Repr_0__Nat_reprFast(x_29);
x_153 = lean_string_append(x_151, x_152);
lean_dec(x_152);
x_154 = lean_mk_string_unchecked("]", 1, 1);
x_155 = lean_string_append(x_153, x_154);
lean_dec(x_154);
x_156 = lean_string_append(x_155, x_143);
x_157 = lean_mk_string_unchecked(" ", 1, 1);
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_string_append(x_158, x_139);
lean_dec(x_139);
x_160 = lean_string_append(x_159, x_157);
lean_dec(x_157);
x_161 = lean_string_append(x_160, x_68);
lean_dec(x_68);
if (x_39 == 0)
{
x_71 = x_134;
x_72 = x_136;
x_73 = x_135;
x_74 = x_137;
x_75 = x_138;
x_76 = x_144;
x_77 = x_141;
x_78 = x_161;
goto block_122;
}
else
{
if (x_138 == 0)
{
lean_object* x_162; 
x_162 = lean_mk_string_unchecked("32", 2, 2);
x_123 = x_134;
x_124 = x_135;
x_125 = x_136;
x_126 = x_161;
x_127 = x_137;
x_128 = x_138;
x_129 = x_144;
x_130 = x_141;
x_131 = x_162;
goto block_133;
}
else
{
lean_object* x_163; 
x_163 = l_Lake_LogLevel_ansiColor(x_142);
x_123 = x_134;
x_124 = x_135;
x_125 = x_136;
x_126 = x_161;
x_127 = x_137;
x_128 = x_138;
x_129 = x_144;
x_130 = x_141;
x_131 = x_163;
goto block_133;
}
}
}
block_177:
{
if (x_170 == 0)
{
lean_object* x_175; 
x_175 = lean_mk_string_unchecked("", 0, 0);
x_134 = x_165;
x_135 = x_167;
x_136 = x_166;
x_137 = x_168;
x_138 = x_169;
x_139 = x_171;
x_140 = x_174;
x_141 = x_172;
x_142 = x_173;
x_143 = x_175;
goto block_164;
}
else
{
lean_object* x_176; 
x_176 = lean_mk_string_unchecked(" (Optional)", 11, 11);
x_134 = x_165;
x_135 = x_167;
x_136 = x_166;
x_137 = x_168;
x_138 = x_169;
x_139 = x_171;
x_140 = x_174;
x_141 = x_172;
x_142 = x_173;
x_143 = x_176;
goto block_164;
}
}
block_188:
{
uint32_t x_187; 
x_187 = l_Lake_LogLevel_icon(x_185);
x_165 = x_178;
x_166 = x_180;
x_167 = x_179;
x_168 = x_181;
x_169 = x_186;
x_170 = x_183;
x_171 = x_182;
x_172 = x_184;
x_173 = x_185;
x_174 = x_187;
goto block_177;
}
block_200:
{
lean_object* x_198; uint32_t x_199; 
x_198 = lean_unsigned_to_nat(10004u);
x_199 = l_Char_ofNat(x_198);
x_165 = x_189;
x_166 = x_191;
x_167 = x_190;
x_168 = x_192;
x_169 = x_197;
x_170 = x_194;
x_171 = x_193;
x_172 = x_195;
x_173 = x_196;
x_174 = x_199;
goto block_177;
}
block_230:
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_212 = lean_array_get_size(x_204);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_nat_dec_eq(x_212, x_213);
lean_dec(x_212);
x_215 = l_instDecidableNot___redArg(x_214);
if (x_215 == 0)
{
uint8_t x_216; lean_object* x_217; uint8_t x_218; uint8_t x_219; 
x_216 = lean_unbox(x_202);
x_217 = l_Lake_JobAction_verb(x_216, x_207);
x_218 = lean_unbox(x_202);
x_219 = lean_unbox(x_202);
x_189 = x_203;
x_190 = x_218;
x_191 = x_204;
x_192 = x_205;
x_193 = x_217;
x_194 = x_206;
x_195 = x_210;
x_196 = x_211;
x_197 = x_219;
goto block_200;
}
else
{
if (x_209 == 0)
{
uint8_t x_220; lean_object* x_221; 
x_220 = lean_unbox(x_202);
x_221 = l_Lake_JobAction_verb(x_220, x_207);
if (x_208 == 0)
{
uint8_t x_222; uint8_t x_223; 
x_222 = lean_unbox(x_202);
x_223 = lean_unbox(x_202);
x_189 = x_203;
x_190 = x_222;
x_191 = x_204;
x_192 = x_205;
x_193 = x_221;
x_194 = x_206;
x_195 = x_210;
x_196 = x_211;
x_197 = x_223;
goto block_200;
}
else
{
uint8_t x_224; uint8_t x_225; 
x_224 = lean_unbox(x_202);
x_225 = lean_unbox(x_201);
x_178 = x_203;
x_179 = x_224;
x_180 = x_204;
x_181 = x_205;
x_182 = x_221;
x_183 = x_206;
x_184 = x_210;
x_185 = x_211;
x_186 = x_225;
goto block_188;
}
}
else
{
uint8_t x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_226 = lean_unbox(x_201);
x_227 = l_Lake_JobAction_verb(x_226, x_207);
x_228 = lean_unbox(x_201);
x_229 = lean_unbox(x_201);
x_178 = x_203;
x_179 = x_228;
x_180 = x_204;
x_181 = x_205;
x_182 = x_227;
x_183 = x_206;
x_184 = x_210;
x_185 = x_211;
x_186 = x_229;
goto block_188;
}
}
}
block_243:
{
uint8_t x_242; 
x_242 = l_instDecidableNot___redArg(x_241);
if (x_242 == 0)
{
lean_dec(x_238);
lean_dec(x_232);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_231;
x_6 = x_233;
goto block_10;
}
else
{
if (x_240 == 0)
{
lean_dec(x_238);
lean_dec(x_232);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_231;
x_6 = x_233;
goto block_10;
}
else
{
x_203 = x_231;
x_204 = x_232;
x_205 = x_233;
x_206 = x_234;
x_207 = x_235;
x_208 = x_237;
x_209 = x_236;
x_210 = x_238;
x_211 = x_239;
goto block_230;
}
}
}
block_256:
{
if (x_40 == 0)
{
lean_dec(x_251);
lean_dec(x_245);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_244;
x_6 = x_246;
goto block_10;
}
else
{
if (x_39 == 0)
{
uint8_t x_254; 
x_254 = lean_unbox(x_202);
x_231 = x_244;
x_232 = x_245;
x_233 = x_246;
x_234 = x_247;
x_235 = x_248;
x_236 = x_250;
x_237 = x_249;
x_238 = x_251;
x_239 = x_253;
x_240 = x_252;
x_241 = x_254;
goto block_243;
}
else
{
uint8_t x_255; 
x_255 = lean_unbox(x_201);
x_231 = x_244;
x_232 = x_245;
x_233 = x_246;
x_234 = x_247;
x_235 = x_248;
x_236 = x_250;
x_237 = x_249;
x_238 = x_251;
x_239 = x_253;
x_240 = x_252;
x_241 = x_255;
goto block_243;
}
}
}
block_271:
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; 
x_267 = lean_array_get_size(x_258);
x_268 = lean_unsigned_to_nat(0u);
x_269 = lean_nat_dec_eq(x_267, x_268);
lean_dec(x_267);
x_270 = l_instDecidableNot___redArg(x_269);
if (x_270 == 0)
{
x_244 = x_257;
x_245 = x_258;
x_246 = x_259;
x_247 = x_260;
x_248 = x_261;
x_249 = x_263;
x_250 = x_262;
x_251 = x_264;
x_252 = x_266;
x_253 = x_265;
goto block_256;
}
else
{
if (x_263 == 0)
{
x_244 = x_257;
x_245 = x_258;
x_246 = x_259;
x_247 = x_260;
x_248 = x_261;
x_249 = x_263;
x_250 = x_262;
x_251 = x_264;
x_252 = x_266;
x_253 = x_265;
goto block_256;
}
else
{
x_203 = x_257;
x_204 = x_258;
x_205 = x_259;
x_206 = x_260;
x_207 = x_261;
x_208 = x_263;
x_209 = x_262;
x_210 = x_264;
x_211 = x_265;
goto block_230;
}
}
}
block_286:
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; uint8_t x_285; 
x_282 = lean_array_get_size(x_273);
x_283 = lean_unsigned_to_nat(0u);
x_284 = lean_nat_dec_eq(x_282, x_283);
lean_dec(x_282);
x_285 = l_instDecidableNot___redArg(x_284);
if (x_285 == 0)
{
x_257 = x_272;
x_258 = x_273;
x_259 = x_274;
x_260 = x_275;
x_261 = x_276;
x_262 = x_278;
x_263 = x_277;
x_264 = x_279;
x_265 = x_281;
x_266 = x_280;
goto block_271;
}
else
{
if (x_278 == 0)
{
x_257 = x_272;
x_258 = x_273;
x_259 = x_274;
x_260 = x_275;
x_261 = x_276;
x_262 = x_278;
x_263 = x_277;
x_264 = x_279;
x_265 = x_281;
x_266 = x_280;
goto block_271;
}
else
{
x_203 = x_272;
x_204 = x_273;
x_205 = x_274;
x_206 = x_275;
x_207 = x_276;
x_208 = x_277;
x_209 = x_278;
x_210 = x_279;
x_211 = x_281;
goto block_230;
}
}
}
block_298:
{
uint8_t x_297; 
x_297 = l_instDecidableNot___redArg(x_296);
if (x_297 == 0)
{
if (x_38 == 0)
{
lean_dec(x_293);
lean_dec(x_288);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_28);
x_5 = x_287;
x_6 = x_289;
goto block_10;
}
else
{
x_272 = x_287;
x_273 = x_288;
x_274 = x_289;
x_275 = x_296;
x_276 = x_290;
x_277 = x_291;
x_278 = x_292;
x_279 = x_293;
x_280 = x_294;
x_281 = x_295;
goto block_286;
}
}
else
{
x_272 = x_287;
x_273 = x_288;
x_274 = x_289;
x_275 = x_296;
x_276 = x_290;
x_277 = x_291;
x_278 = x_292;
x_279 = x_293;
x_280 = x_294;
x_281 = x_295;
goto block_286;
}
}
block_310:
{
if (x_69 == 0)
{
uint8_t x_308; 
x_308 = lean_unbox(x_202);
x_287 = x_307;
x_288 = x_299;
x_289 = x_306;
x_290 = x_300;
x_291 = x_302;
x_292 = x_301;
x_293 = x_305;
x_294 = x_304;
x_295 = x_303;
x_296 = x_308;
goto block_298;
}
else
{
uint8_t x_309; 
x_309 = lean_unbox(x_201);
x_287 = x_307;
x_288 = x_299;
x_289 = x_306;
x_290 = x_300;
x_291 = x_302;
x_292 = x_301;
x_293 = x_305;
x_294 = x_304;
x_295 = x_303;
x_296 = x_309;
goto block_298;
}
}
block_329:
{
uint8_t x_318; 
x_318 = l_instDecidableNot___redArg(x_317);
if (x_318 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_299 = x_311;
x_300 = x_312;
x_301 = x_314;
x_302 = x_313;
x_303 = x_316;
x_304 = x_315;
x_305 = x_2;
x_306 = x_3;
x_307 = x_4;
goto block_310;
}
else
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_3);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_320 = lean_ctor_get(x_3, 5);
lean_dec(x_320);
x_321 = lean_ctor_get(x_3, 4);
lean_dec(x_321);
x_322 = lean_ctor_get(x_3, 3);
lean_dec(x_322);
x_323 = lean_ctor_get(x_3, 2);
lean_dec(x_323);
x_324 = lean_ctor_get(x_3, 1);
lean_dec(x_324);
x_325 = lean_ctor_get(x_3, 0);
lean_dec(x_325);
lean_inc(x_68);
x_326 = lean_array_push(x_30, x_68);
lean_inc(x_29);
lean_inc(x_28);
lean_ctor_set(x_3, 2, x_326);
x_299 = x_311;
x_300 = x_312;
x_301 = x_314;
x_302 = x_313;
x_303 = x_316;
x_304 = x_315;
x_305 = x_2;
x_306 = x_3;
x_307 = x_4;
goto block_310;
}
else
{
lean_object* x_327; lean_object* x_328; 
lean_dec(x_3);
lean_inc(x_68);
x_327 = lean_array_push(x_30, x_68);
lean_inc(x_29);
lean_inc(x_28);
x_328 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_328, 0, x_28);
lean_ctor_set(x_328, 1, x_29);
lean_ctor_set(x_328, 2, x_327);
lean_ctor_set(x_328, 3, x_31);
lean_ctor_set(x_328, 4, x_32);
lean_ctor_set(x_328, 5, x_33);
x_299 = x_311;
x_300 = x_312;
x_301 = x_314;
x_302 = x_313;
x_303 = x_316;
x_304 = x_315;
x_305 = x_2;
x_306 = x_328;
x_307 = x_4;
goto block_310;
}
}
}
block_351:
{
lean_object* x_333; uint8_t x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_348; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get_uint8(x_332, sizeof(void*)*2);
lean_dec(x_332);
x_335 = l_Lake_Log_maxLv(x_333);
x_336 = lean_box(x_37);
x_337 = lean_box(x_334);
x_338 = l_Ord_instDecidableRelLe___redArg(x_330, x_336, x_337);
x_339 = lean_box(x_35);
x_340 = lean_box(x_335);
x_341 = l_Ord_instDecidableRelLe___redArg(x_331, x_339, x_340);
x_342 = lean_box(x_36);
x_343 = lean_box(x_335);
x_344 = l_Ord_instDecidableRelLe___redArg(x_331, x_342, x_343);
x_345 = lean_array_get_size(x_333);
x_346 = lean_unsigned_to_nat(0u);
x_347 = lean_nat_dec_eq(x_345, x_346);
lean_dec(x_345);
x_348 = l_instDecidableNot___redArg(x_347);
if (x_348 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_299 = x_333;
x_300 = x_334;
x_301 = x_344;
x_302 = x_341;
x_303 = x_335;
x_304 = x_338;
x_305 = x_2;
x_306 = x_3;
x_307 = x_4;
goto block_310;
}
else
{
if (x_344 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_299 = x_333;
x_300 = x_334;
x_301 = x_344;
x_302 = x_341;
x_303 = x_335;
x_304 = x_338;
x_305 = x_2;
x_306 = x_3;
x_307 = x_4;
goto block_310;
}
else
{
if (x_69 == 0)
{
uint8_t x_349; 
x_349 = lean_unbox(x_202);
x_311 = x_333;
x_312 = x_334;
x_313 = x_341;
x_314 = x_344;
x_315 = x_338;
x_316 = x_335;
x_317 = x_349;
goto block_329;
}
else
{
uint8_t x_350; 
x_350 = lean_unbox(x_201);
x_311 = x_333;
x_312 = x_334;
x_313 = x_341;
x_314 = x_344;
x_315 = x_338;
x_316 = x_335;
x_317 = x_350;
goto block_329;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___redArg(x_1, x_10, x_11, x_4, x_12, x_13, x_7, x_8, x_9);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_reportJob_spec__0(x_1, x_11, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = lean_array_uget(x_1, x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_io_get_task_state(x_20, x_7);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
switch (x_23) {
case 0:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_4, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_array_push(x_18, x_19);
lean_ctor_set(x_4, 1, x_28);
x_8 = x_4;
x_9 = x_6;
x_10 = x_27;
goto block_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_array_push(x_18, x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_30);
x_8 = x_31;
x_9 = x_6;
x_10 = x_29;
goto block_15;
}
}
case 1:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
lean_inc(x_19);
x_36 = lean_array_push(x_17, x_19);
x_37 = lean_array_push(x_18, x_19);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_36);
x_8 = x_4;
x_9 = x_6;
x_10 = x_35;
goto block_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_dec(x_21);
lean_inc(x_19);
x_39 = lean_array_push(x_17, x_19);
x_40 = lean_array_push(x_18, x_19);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_8 = x_41;
x_9 = x_6;
x_10 = x_38;
goto block_15;
}
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_18);
lean_dec(x_17);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_dec(x_21);
lean_inc(x_5);
x_43 = l_Lake_Monitor_reportJob(x_19, x_5, x_6, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_47, x_48);
lean_dec(x_47);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 5);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_50);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_53);
lean_ctor_set(x_55, 5, x_54);
x_8 = x_4;
x_9 = x_55;
x_10 = x_45;
goto block_15;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_6);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_7);
return x_57;
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_8;
x_6 = x_9;
x_7 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_poll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_st_ref_take(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_inc(x_11);
x_12 = lean_st_ref_set(x_5, x_11, x_9);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_array_get_size(x_8);
x_29 = lean_nat_add(x_17, x_18);
x_30 = lean_ctor_get(x_3, 2);
x_31 = lean_ctor_get(x_3, 3);
x_32 = lean_ctor_get(x_3, 4);
x_33 = lean_ctor_get(x_3, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_16);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_32);
lean_ctor_set(x_34, 5, x_33);
lean_inc(x_11);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_11);
x_35 = lean_array_get_size(x_1);
x_36 = lean_nat_dec_lt(x_10, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_inc(x_34);
lean_inc(x_6);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_34);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_37);
x_19 = x_12;
x_20 = x_6;
x_21 = x_34;
x_22 = x_14;
goto block_28;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_35, x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_inc(x_34);
lean_inc(x_6);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_34);
lean_inc(x_14);
lean_ctor_set(x_12, 0, x_39);
x_19 = x_12;
x_20 = x_6;
x_21 = x_34;
x_22 = x_14;
goto block_28;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_12);
x_40 = lean_usize_of_nat(x_10);
x_41 = lean_usize_of_nat(x_35);
lean_dec(x_35);
lean_inc(x_2);
x_42 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_40, x_41, x_6, x_2, x_34, x_14);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_19 = x_42;
x_20 = x_45;
x_21 = x_46;
x_22 = x_44;
goto block_28;
}
}
block_28:
{
uint8_t x_23; 
x_23 = lean_nat_dec_lt(x_10, x_18);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_18, x_18);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
return x_19;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
lean_dec(x_19);
x_25 = lean_usize_of_nat(x_10);
x_26 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_27 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_8, x_25, x_26, x_20, x_2, x_21, x_22);
lean_dec(x_8);
return x_27;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_array_get_size(x_8);
x_61 = lean_nat_add(x_49, x_50);
x_62 = lean_ctor_get(x_3, 2);
x_63 = lean_ctor_get(x_3, 3);
x_64 = lean_ctor_get(x_3, 4);
x_65 = lean_ctor_get(x_3, 5);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_48);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_48);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_63);
lean_ctor_set(x_66, 4, x_64);
lean_ctor_set(x_66, 5, x_65);
lean_inc(x_11);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_11);
x_67 = lean_array_get_size(x_1);
x_68 = lean_nat_dec_lt(x_10, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_inc(x_66);
lean_inc(x_6);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_6);
lean_ctor_set(x_69, 1, x_66);
lean_inc(x_47);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_47);
x_51 = x_70;
x_52 = x_6;
x_53 = x_66;
x_54 = x_47;
goto block_60;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_67, x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_67);
lean_inc(x_66);
lean_inc(x_6);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_6);
lean_ctor_set(x_72, 1, x_66);
lean_inc(x_47);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_47);
x_51 = x_73;
x_52 = x_6;
x_53 = x_66;
x_54 = x_47;
goto block_60;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_usize_of_nat(x_10);
x_75 = lean_usize_of_nat(x_67);
lean_dec(x_67);
lean_inc(x_2);
x_76 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_74, x_75, x_6, x_2, x_66, x_47);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_51 = x_76;
x_52 = x_79;
x_53 = x_80;
x_54 = x_78;
goto block_60;
}
}
block_60:
{
uint8_t x_55; 
x_55 = lean_nat_dec_lt(x_10, x_50);
if (x_55 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_2);
return x_51;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_50, x_50);
if (x_56 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_2);
return x_51;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
lean_dec(x_51);
x_57 = lean_usize_of_nat(x_10);
x_58 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_59 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_8, x_57, x_58, x_52, x_2, x_53, x_54);
lean_dec(x_8);
return x_59;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_81 = lean_ctor_get(x_6, 0);
x_82 = lean_ctor_get(x_6, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_6);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_mk_empty_array_with_capacity(x_83);
lean_inc(x_84);
x_85 = lean_st_ref_set(x_5, x_84, x_82);
lean_dec(x_5);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_3, 0);
x_89 = lean_ctor_get(x_3, 1);
x_90 = lean_array_get_size(x_81);
x_101 = lean_nat_add(x_89, x_90);
x_102 = lean_ctor_get(x_3, 2);
x_103 = lean_ctor_get(x_3, 3);
x_104 = lean_ctor_get(x_3, 4);
x_105 = lean_ctor_get(x_3, 5);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_88);
x_106 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_106, 0, x_88);
lean_ctor_set(x_106, 1, x_101);
lean_ctor_set(x_106, 2, x_102);
lean_ctor_set(x_106, 3, x_103);
lean_ctor_set(x_106, 4, x_104);
lean_ctor_set(x_106, 5, x_105);
lean_inc(x_84);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_84);
lean_ctor_set(x_107, 1, x_84);
x_108 = lean_array_get_size(x_1);
x_109 = lean_nat_dec_lt(x_83, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_108);
lean_inc(x_106);
lean_inc(x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_106);
lean_inc(x_86);
if (lean_is_scalar(x_87)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_87;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_86);
x_91 = x_111;
x_92 = x_107;
x_93 = x_106;
x_94 = x_86;
goto block_100;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_108, x_108);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_108);
lean_inc(x_106);
lean_inc(x_107);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_106);
lean_inc(x_86);
if (lean_is_scalar(x_87)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_87;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_86);
x_91 = x_114;
x_92 = x_107;
x_93 = x_106;
x_94 = x_86;
goto block_100;
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_87);
x_115 = lean_usize_of_nat(x_83);
x_116 = lean_usize_of_nat(x_108);
lean_dec(x_108);
lean_inc(x_2);
x_117 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_115, x_116, x_107, x_2, x_106, x_86);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_91 = x_117;
x_92 = x_120;
x_93 = x_121;
x_94 = x_119;
goto block_100;
}
}
block_100:
{
uint8_t x_95; 
x_95 = lean_nat_dec_lt(x_83, x_90);
if (x_95 == 0)
{
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_81);
lean_dec(x_2);
return x_91;
}
else
{
uint8_t x_96; 
x_96 = lean_nat_dec_le(x_90, x_90);
if (x_96 == 0)
{
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_81);
lean_dec(x_2);
return x_91;
}
else
{
size_t x_97; size_t x_98; lean_object* x_99; 
lean_dec(x_91);
x_97 = lean_usize_of_nat(x_83);
x_98 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_99 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_81, x_97, x_98, x_92, x_2, x_93, x_94);
lean_dec(x_81);
return x_99;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Monitor_poll_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_poll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_io_mono_ms_now(x_3);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_2, 4);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_nat_sub(x_30, x_32);
lean_dec(x_30);
x_35 = lean_nat_sub(x_33, x_34);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
x_4 = x_2;
x_5 = x_31;
goto block_28;
}
else
{
uint32_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_uint32_of_nat(x_35);
lean_dec(x_35);
x_39 = l_IO_sleep(x_38, x_31);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_4 = x_2;
x_5 = x_40;
goto block_28;
}
block_28:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_io_mono_ms_now(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_15, 4, x_8);
lean_ctor_set(x_15, 5, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_ctor_get(x_4, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_sleep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Monitor_sleep(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
x_5 = l_Lake_Monitor_poll(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_18 = lean_box(0);
lean_ctor_set(x_7, 1, x_11);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_5, 0, x_7);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_7);
lean_free_object(x_5);
lean_inc(x_2);
x_19 = l_Lake_Monitor_renderProgress___redArg(x_13, x_14, x_2, x_11, x_9);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lake_Monitor_sleep(x_2, x_22, x_21);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_1 = x_14;
x_3 = x_26;
x_4 = x_25;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_5);
lean_inc(x_2);
x_35 = l_Lake_Monitor_renderProgress___redArg(x_28, x_29, x_2, x_11, x_9);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lake_Monitor_sleep(x_2, x_38, x_37);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_1 = x_29;
x_3 = x_42;
x_4 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_48 = x_7;
} else {
 lean_dec_ref(x_7);
 x_48 = lean_box(0);
}
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_47);
x_51 = lean_nat_dec_lt(x_49, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
x_52 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_48);
lean_inc(x_2);
x_55 = l_Lake_Monitor_renderProgress___redArg(x_46, x_47, x_2, x_45, x_44);
lean_dec(x_46);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lake_Monitor_sleep(x_2, x_58, x_57);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_1 = x_47;
x_3 = x_62;
x_4 = x_61;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Monitor_main___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc(x_2);
x_5 = l_Lake_Monitor_loop(x_1, x_2, x_3, x_4);
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
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_ctor_get(x_9, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 5);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
x_33 = lean_string_utf8_byte_size(x_11);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_instDecidableEqPos(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 4);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_11);
x_38 = lean_apply_2(x_37, x_11, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_11);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_24 = x_39;
goto block_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(x_35);
x_43 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_45 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_46 = lean_unsigned_to_nat(79u);
x_47 = lean_unsigned_to_nat(4u);
x_48 = lean_mk_string_unchecked("[", 1, 1);
x_49 = lean_mk_string_unchecked("Lake", 4, 4);
x_50 = lean_mk_string_unchecked("print!", 6, 6);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
x_54 = l_Lean_Name_toString(x_51, x_53, x_43);
x_55 = lean_string_append(x_48, x_54);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = lean_io_error_to_string(x_40);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = lean_mk_string_unchecked("] ", 2, 2);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
x_62 = l_String_quote(x_11);
lean_dec(x_11);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_unsigned_to_nat(120u);
x_65 = lean_format_pretty(x_63, x_64, x_34, x_34);
x_66 = lean_string_append(x_61, x_65);
lean_dec(x_65);
x_67 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_44, x_45, x_46, x_47, x_66);
lean_dec(x_66);
lean_dec(x_45);
lean_dec(x_44);
x_68 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_67, x_41);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_24 = x_69;
goto block_32;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_18);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_7);
return x_72;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_10)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_10;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_18);
if (lean_is_scalar(x_8)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_8;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
block_32:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_1(x_26, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_19 = x_28;
x_20 = x_29;
goto block_23;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_19 = x_31;
x_20 = x_30;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Monitor_main___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Monitor_main___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_io_mono_ms_now(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 3, 6);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 1, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 2, x_6);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 3, x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 4, x_8);
lean_ctor_set_uint8(x_17, sizeof(void*)*3 + 5, x_9);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_10);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 5, x_18);
x_20 = l_Lake_Monitor_main(x_1, x_17, x_19, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_monitorJobs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l_Lake_monitorJobs(x_1, x_2, x_3, x_14, x_15, x_16, x_17, x_18, x_19, x_10, x_11, x_12, x_13);
return x_20;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_get_set_stderr(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_19);
x_22 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_21, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
lean_inc(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_16, x_25, x_28, x_27, x_24);
lean_dec(x_27);
lean_dec(x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_26);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_box(0);
x_45 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_16, x_25, x_44, x_43, x_24);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_9 = x_42;
x_10 = x_48;
x_11 = x_47;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_get_set_stdout(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_19);
x_22 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_21, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
lean_inc(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_16, x_25, x_28, x_27, x_24);
lean_dec(x_27);
lean_dec(x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_26);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_box(0);
x_45 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_16, x_25, x_44, x_43, x_24);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_9 = x_42;
x_10 = x_48;
x_11 = x_47;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_get_set_stdin(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_19);
x_22 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_21, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
lean_inc(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_16, x_25, x_28, x_27, x_24);
lean_dec(x_27);
lean_dec(x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_26);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_box(0);
x_45 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_16, x_25, x_44, x_43, x_24);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_9 = x_42;
x_10 = x_48;
x_11 = x_47;
goto block_14;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_6(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_17 = l_ByteArray_empty;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_19);
x_20 = lean_st_mk_ref(x_19, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_mk_ref(x_19, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_26);
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_27);
x_30 = l_IO_FS_Stream_ofBuffer(x_21);
lean_inc(x_24);
x_31 = l_IO_FS_Stream_ofBuffer(x_24);
x_32 = lean_box(x_2);
lean_inc(x_31);
x_33 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_1);
lean_closure_set(x_33, 2, x_31);
x_34 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___boxed), 9, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, x_31);
lean_closure_set(x_34, 2, x_33);
x_35 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(x_30, x_34, x_3, x_4, x_5, x_6, x_29, x_25);
lean_dec(x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_st_ref_get(x_24, x_37);
lean_dec(x_24);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_44);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
lean_dec(x_41);
x_48 = lean_string_validate_utf8(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
x_50 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
x_51 = lean_unsigned_to_nat(128u);
x_52 = lean_unsigned_to_nat(47u);
x_53 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
x_54 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_49, x_50, x_51, x_52, x_53);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_49);
x_55 = l_panic___at___Lean_Name_getString_x21_spec__0(x_54);
x_9 = x_42;
x_10 = x_38;
x_11 = x_46;
x_12 = x_55;
goto block_16;
}
else
{
lean_object* x_56; 
x_56 = lean_string_from_utf8_unchecked(x_47);
lean_dec(x_47);
x_9 = x_42;
x_10 = x_38;
x_11 = x_46;
x_12 = x_56;
goto block_16;
}
}
else
{
uint8_t x_57; 
lean_dec(x_24);
x_57 = !lean_is_exclusive(x_35);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_35, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_36);
if (x_59 == 0)
{
return x_35;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_36, 0);
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_36);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_35, 0, x_62);
return x_35;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
lean_dec(x_35);
x_64 = lean_ctor_get(x_36, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_36, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_66 = x_36;
} else {
 lean_dec_ref(x_36);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_4, x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_4);
x_17 = lean_mk_string_unchecked("- ", 2, 2);
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("\n", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_inc(x_20);
x_22 = lean_apply_2(x_21, x_20, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_8 = x_23;
x_9 = x_24;
goto block_14;
}
else
{
lean_dec(x_1);
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(x_2);
x_28 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_30 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_31 = lean_unsigned_to_nat(79u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_mk_string_unchecked("[", 1, 1);
x_34 = lean_mk_string_unchecked("Lake", 4, 4);
x_35 = lean_mk_string_unchecked("print!", 6, 6);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Name_toString(x_36, x_38, x_28);
x_40 = lean_string_append(x_33, x_39);
lean_dec(x_39);
x_41 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = lean_io_error_to_string(x_25);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked("] ", 2, 2);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = l_String_quote(x_20);
lean_dec(x_20);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unsigned_to_nat(120u);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_format_pretty(x_48, x_49, x_50, x_50);
x_52 = lean_string_append(x_46, x_51);
lean_dec(x_51);
x_53 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_52);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
x_54 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_53, x_26);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_8 = x_55;
x_9 = x_56;
goto block_14;
}
}
else
{
lean_object* x_57; 
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_6);
lean_ctor_set(x_57, 1, x_7);
return x_57;
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_6 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_4, x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_4);
x_17 = lean_mk_string_unchecked("- ", 2, 2);
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("\n", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_inc(x_20);
x_22 = lean_apply_2(x_21, x_20, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_8 = x_23;
x_9 = x_24;
goto block_14;
}
else
{
lean_dec(x_1);
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(x_2);
x_28 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___lam__0___boxed), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_30 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_31 = lean_unsigned_to_nat(79u);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_mk_string_unchecked("[", 1, 1);
x_34 = lean_mk_string_unchecked("Lake", 4, 4);
x_35 = lean_mk_string_unchecked("print!", 6, 6);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Name_toString(x_36, x_38, x_28);
x_40 = lean_string_append(x_33, x_39);
lean_dec(x_39);
x_41 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = lean_io_error_to_string(x_25);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked("] ", 2, 2);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = l_String_quote(x_20);
lean_dec(x_20);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unsigned_to_nat(120u);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_format_pretty(x_48, x_49, x_50, x_50);
x_52 = lean_string_append(x_46, x_51);
lean_dec(x_51);
x_53 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_52);
lean_dec(x_52);
lean_dec(x_30);
lean_dec(x_29);
x_54 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_53, x_26);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_8 = x_55;
x_9 = x_56;
goto block_14;
}
}
else
{
lean_object* x_57; 
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_6);
lean_ctor_set(x_57, 1, x_7);
return x_57;
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_4, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(x_1, x_2, x_3, x_12, x_5, x_8, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
lean_ctor_set(x_10, 1, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_27 = x_10;
} else {
 lean_dec_ref(x_10);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_28);
if (lean_is_scalar(x_27)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_27;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_9, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_10, 1);
x_37 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_37);
lean_ctor_set(x_10, 1, x_39);
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_9, 0, x_45);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_dec(x_9);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_49 = x_10;
} else {
 lean_dec_ref(x_10);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_dec(x_6);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_50);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
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
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_24 = lean_string_utf8_byte_size(x_17);
x_25 = l_instDecidableEqPos(x_24, x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_27 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_17, x_24, x_8);
x_28 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_17, x_27, x_24);
x_29 = lean_string_utf8_extract(x_17, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
x_35 = lean_array_push(x_34, x_32);
x_36 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_36);
x_19 = x_38;
x_20 = x_13;
goto block_23;
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_8);
x_19 = x_15;
x_20 = x_13;
goto block_23;
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_14;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_10, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_10, 0, x_44);
return x_10;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_48 = x_11;
} else {
 lean_dec_ref(x_11);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; uint8_t x_138; uint8_t x_139; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = l_Lake_OutStream_get(x_10, x_4);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_inc(x_12);
x_20 = l_Lake_AnsiMode_isEnabled(x_12, x_19, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_3);
x_23 = l_Lake_mkBuildContext(x_1, x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_st_mk_ref(x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__0), 7, 1);
lean_closure_set(x_30, 0, x_2);
x_31 = lean_unsigned_to_nat(0u);
x_48 = lean_box(0);
x_49 = lean_alloc_closure((void*)(l_Lake_recFetchWithIndex), 6, 0);
x_50 = lean_mk_empty_array_with_capacity(x_31);
x_51 = lean_box(0);
x_52 = lean_mk_string_unchecked("<nil>", 5, 5);
x_53 = l_Lake_BuildTrace_nil(x_52);
lean_inc(x_50);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_unbox(x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_55);
x_56 = lean_box(1);
lean_inc(x_24);
lean_inc(x_28);
x_57 = lean_alloc_closure((void*)(l_Lake_Workspace_runFetchM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(x_57, 0, x_30);
lean_closure_set(x_57, 1, x_56);
lean_closure_set(x_57, 2, x_49);
lean_closure_set(x_57, 3, x_48);
lean_closure_set(x_57, 4, x_28);
lean_closure_set(x_57, 5, x_24);
lean_closure_set(x_57, 6, x_54);
lean_closure_set(x_57, 7, x_31);
x_58 = lean_io_as_task(x_57, x_31, x_29);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_get(x_28, x_60);
lean_dec(x_28);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_64 = lean_mk_string_unchecked("job computation", 15, 15);
x_65 = lean_box(0);
x_66 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_67 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_68 = l_Lake_BuildConfig_showProgress(x_3);
lean_inc(x_59);
x_69 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_63);
lean_ctor_set(x_69, 2, x_64);
x_70 = lean_unbox(x_65);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_70);
x_71 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
lean_dec(x_3);
x_72 = lean_box(2);
x_138 = lean_unbox(x_72);
x_139 = l_Lake_instDecidableEqVerbosity(x_71, x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_box(2);
x_141 = lean_unbox(x_140);
x_73 = x_141;
goto block_137;
}
else
{
uint8_t x_142; 
x_142 = lean_unbox(x_51);
x_73 = x_142;
goto block_137;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("build failed", 12, 12);
x_7 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_apply_1(x_15, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_5 = x_17;
goto block_9;
}
block_47:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_array_get_size(x_33);
x_36 = lean_nat_dec_lt(x_31, x_35);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_14 = x_34;
goto block_18;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_35, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_14 = x_34;
goto block_18;
}
else
{
lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_usize_of_nat(x_31);
x_40 = lean_usize_of_nat(x_35);
lean_dec(x_35);
lean_inc(x_12);
x_41 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(x_12, x_32, x_33, x_39, x_40, x_38, x_34);
lean_dec(x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_14 = x_42;
goto block_18;
}
else
{
uint8_t x_43; 
lean_dec(x_12);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
block_137:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_74 = l_Lake_Job_toOpaque___redArg(x_69);
lean_dec(x_69);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_mk_empty_array_with_capacity(x_75);
x_77 = lean_array_push(x_76, x_74);
x_78 = lean_ctor_get(x_24, 3);
lean_inc(x_78);
lean_dec(x_24);
x_79 = lean_unbox(x_72);
x_80 = l_Lake_instDecidableEqVerbosity(x_71, x_79);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = lean_unsigned_to_nat(100u);
x_83 = lean_unbox(x_21);
lean_dec(x_21);
lean_inc(x_12);
x_84 = l_Lake_monitorJobs(x_77, x_78, x_12, x_67, x_66, x_73, x_80, x_83, x_68, x_81, x_50, x_82, x_62);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Array_isEmpty___redArg(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_59);
x_88 = lean_mk_string_unchecked("Some required builds logged failures:\n", 38, 38);
x_89 = lean_ctor_get(x_12, 4);
lean_inc(x_89);
lean_inc(x_88);
x_90 = lean_apply_2(x_89, x_88, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec(x_88);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_32 = x_87;
x_33 = x_85;
x_34 = x_91;
goto block_47;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_box(x_87);
x_95 = lean_alloc_closure((void*)(l_Lake_Monitor_main___lam__0___boxed), 2, 1);
lean_closure_set(x_95, 0, x_94);
x_96 = lean_mk_string_unchecked("Lake.Build.Run", 14, 14);
x_97 = lean_mk_string_unchecked("Lake.print!", 11, 11);
x_98 = lean_unsigned_to_nat(79u);
x_99 = lean_unsigned_to_nat(4u);
x_100 = lean_mk_string_unchecked("[", 1, 1);
x_101 = lean_mk_string_unchecked("Lake", 4, 4);
x_102 = lean_mk_string_unchecked("print!", 6, 6);
x_103 = l_Lean_Name_mkStr2(x_101, x_102);
x_104 = lean_unbox(x_56);
x_105 = l_Lean_Name_toString(x_103, x_104, x_95);
x_106 = lean_string_append(x_100, x_105);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked(" failed: ", 9, 9);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = lean_io_error_to_string(x_92);
x_110 = lean_string_append(x_108, x_109);
lean_dec(x_109);
x_111 = lean_mk_string_unchecked("] ", 2, 2);
x_112 = lean_string_append(x_110, x_111);
lean_dec(x_111);
x_113 = l_String_quote(x_88);
lean_dec(x_88);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_unsigned_to_nat(120u);
x_116 = lean_format_pretty(x_114, x_115, x_31, x_31);
x_117 = lean_string_append(x_112, x_116);
lean_dec(x_116);
x_118 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_96, x_97, x_98, x_99, x_117);
lean_dec(x_117);
lean_dec(x_97);
lean_dec(x_96);
x_119 = l_panic___at___Lean_Environment_enableRealizationsForConst_spec__0(x_118, x_93);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_32 = x_87;
x_33 = x_85;
x_34 = x_120;
goto block_47;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_85);
lean_dec(x_12);
x_121 = lean_io_wait(x_59, x_86);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 0);
lean_dec(x_124);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
lean_ctor_set(x_121, 0, x_125);
return x_121;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
lean_dec(x_122);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_dec(x_122);
x_129 = !lean_is_exclusive(x_121);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_121, 0);
lean_dec(x_130);
x_131 = lean_mk_string_unchecked("top-level build failed", 22, 22);
x_132 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set_tag(x_121, 1);
lean_ctor_set(x_121, 0, x_132);
return x_121;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
lean_dec(x_121);
x_134 = lean_mk_string_unchecked("top-level build failed", 22, 22);
x_135 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_Workspace_runFetchM_spec__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4_spec__4(x_1, x_8, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_runFetchM_spec__4(x_1, x_8, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runFetchM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lake_Workspace_runFetchM___redArg___lam__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___redArg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_wait(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_mk_string_unchecked("build failed", 12, 12);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_mk_string_unchecked("build failed", 12, 12);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
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
LEAN_EXPORT lean_object* l_Lake_Workspace_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_io_wait(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = lean_mk_string_unchecked("build failed", 12, 12);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_mk_string_unchecked("build failed", 12, 12);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
return x_6;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_runBuild___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Workspace_runFetchM___redArg(x_3, x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_wait(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_mk_string_unchecked("build failed", 12, 12);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_mk_string_unchecked("build failed", 12, 12);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
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
LEAN_EXPORT lean_object* l_Lake_runBuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_runFetchM___redArg(x_4, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_io_wait(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = lean_mk_string_unchecked("build failed", 12, 12);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_mk_string_unchecked("build failed", 12, 12);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
return x_6;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Index(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Lock(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Index(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Monitor_spinnerFrames = _init_l_Lake_Monitor_spinnerFrames();
lean_mark_persistent(l_Lake_Monitor_spinnerFrames);
l_Lake_Ansi_resetLine = _init_l_Lake_Ansi_resetLine();
lean_mark_persistent(l_Lake_Ansi_resetLine);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
