// Lean compiler output
// Module: Lake.Build.ExternLib
// Imports: Lake.Build.Common
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
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildStatic___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_defaultFacetConfig;
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
extern uint8_t l_System_Platform_isOSX;
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacetConfig___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacetConfig___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_recComputeDynlib___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildFileUnlessUpToDate_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacetConfig;
extern lean_object* l_Lake_sharedLibExt;
extern lean_object* l_Lake_platformTrace;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__0(lean_object*, lean_object*);
uint64_t l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_staticFacetConfig_spec__0(uint8_t, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l_Lake_JobResult_prependLog(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedFacetConfig;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_instDecidableRelPosLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_recComputeDynlib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildStatic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacetConfig;
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
lean_object* l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacetConfig___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_staticFacet;
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_staticFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_defaultFacet;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacetConfig___lam__0(uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_ExternLib_recBuildStatic___lam__1(lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_initFacetConfigs;
extern uint8_t l_System_Platform_isWindows;
extern lean_object* l_Lake_ExternLib_keyword;
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stderr(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stderr(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
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
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdout(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdout(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
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
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_get_set_stdin(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_get_set_stdin(x_1, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg___lam__0(x_16, x_21, x_24, x_23, x_20);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_22);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg___lam__0(x_16, x_21, x_40, x_39, x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_9 = x_38;
x_10 = x_44;
x_11 = x_43;
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
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_11 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_26 = l_IO_FS_Stream_ofBuffer(x_21);
lean_inc(x_24);
x_27 = l_IO_FS_Stream_ofBuffer(x_24);
x_28 = lean_box(x_2);
lean_inc(x_27);
x_29 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_27);
x_30 = lean_alloc_closure((void*)(l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1), 9, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_29);
x_31 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg(x_26, x_30, x_3, x_4, x_5, x_6, x_7, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_st_ref_get(x_24, x_33);
lean_dec(x_24);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_string_validate_utf8(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_39);
x_41 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
x_42 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
x_43 = lean_unsigned_to_nat(128u);
x_44 = lean_unsigned_to_nat(47u);
x_45 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
x_46 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
x_47 = l_panic___at___Lean_Name_getString_x21_spec__0(x_46);
x_9 = x_35;
x_10 = x_38;
x_11 = x_34;
x_12 = x_47;
goto block_16;
}
else
{
lean_object* x_48; 
x_48 = lean_string_from_utf8_unchecked(x_39);
lean_dec(x_39);
x_9 = x_35;
x_10 = x_38;
x_11 = x_34;
x_12 = x_48;
goto block_16;
}
}
else
{
uint8_t x_49; 
lean_dec(x_24);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_31, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_32, 0);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_32);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_31, 0, x_54);
return x_31;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_dec(x_31);
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_58 = x_32;
} else {
 lean_dec_ref(x_32);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l_Lake_instDataKindFilePath;
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_90 = lean_string_utf8_byte_size(x_38);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_instDecidableEqPos(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_94 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_38, x_90, x_91);
x_95 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_38, x_94, x_90);
x_96 = lean_string_utf8_extract(x_38, x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_38);
x_97 = lean_string_append(x_93, x_96);
lean_dec(x_96);
x_98 = lean_box(1);
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
x_100 = lean_unbox(x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_100);
x_101 = lean_box(0);
x_102 = lean_array_push(x_37, x_99);
x_103 = l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_103;
goto block_89;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_38);
x_104 = lean_box(0);
x_105 = l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_105;
goto block_89;
}
block_89:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lake_instDecidableRelPosLt(x_15, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_free_object(x_41);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_40, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
lean_inc(x_45);
x_51 = l_Array_shrink___redArg(x_45, x_15);
x_52 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__0), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_8);
x_57 = lean_task_map(x_53, x_55, x_54, x_56);
x_58 = lean_ctor_get(x_44, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_ctor_set(x_41, 1, x_51);
lean_ctor_set(x_41, 0, x_60);
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_40);
lean_inc(x_45);
x_61 = l_Array_shrink___redArg(x_45, x_15);
x_62 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__0), 2, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_8);
x_67 = lean_task_map(x_63, x_65, x_64, x_66);
x_68 = lean_ctor_get(x_44, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_69);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_41);
lean_ctor_set(x_71, 1, x_42);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_41, 0);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_41);
x_74 = lean_array_get_size(x_73);
x_75 = l_Lake_instDecidableRelPosLt(x_15, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_76 = x_40;
} else {
 lean_dec_ref(x_40);
 x_76 = lean_box(0);
}
lean_inc(x_73);
x_77 = l_Array_shrink___redArg(x_73, x_15);
x_78 = l_Array_extract(lean_box(0), x_73, x_15, x_74);
lean_dec(x_73);
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__0), 2, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_8);
x_83 = lean_task_map(x_79, x_81, x_80, x_82);
x_84 = lean_ctor_get(x_72, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_72, sizeof(void*)*3);
lean_dec(x_72);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_14);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_42);
return x_88;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_dec(x_11);
x_16 = x_106;
x_17 = x_12;
goto block_35;
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract(lean_box(0), x_16, x_15, x_19);
lean_dec(x_16);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = lean_mk_string_unchecked("<nil>", 5, 5);
x_25 = l_Lake_BuildTrace_nil(x_24);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_task_pure(x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_21);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildStatic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_apply_1(x_2, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_apply_1(x_2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_23 = x_10;
} else {
 lean_dec_ref(x_10);
 x_23 = lean_box(0);
}
x_24 = lean_apply_1(x_2, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_9, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_9, 0, x_32);
return x_9;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_36 = x_10;
} else {
 lean_dec_ref(x_10);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_ExternLib_recBuildStatic___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildStatic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_mk_string_unchecked("static", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic___lam__0), 8, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_11);
lean_inc(x_5);
x_15 = l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic___lam__1___boxed), 1, 0);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Name_toString(x_10, x_22, x_20);
x_24 = lean_mk_string_unchecked(":static", 7, 7);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_st_ref_take(x_25, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_29);
x_34 = lean_unbox(x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_34);
x_35 = l_Lake_Job_toOpaque___redArg(x_33);
x_36 = lean_array_push(x_27, x_35);
x_37 = lean_st_ref_set(x_25, x_36, x_28);
lean_dec(x_25);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = l_Lake_Job_renew___redArg(x_33);
lean_ctor_set(x_16, 0, x_40);
lean_ctor_set(x_37, 0, x_16);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = l_Lake_Job_renew___redArg(x_33);
lean_ctor_set(x_16, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic___lam__1___boxed), 1, 0);
x_47 = lean_box(1);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Name_toString(x_10, x_48, x_46);
x_50 = lean_mk_string_unchecked(":static", 7, 7);
x_51 = lean_ctor_get(x_5, 3);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_st_ref_take(x_51, x_17);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_56 = lean_box(0);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
lean_dec(x_44);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_unbox(x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_60);
x_61 = l_Lake_Job_toOpaque___redArg(x_59);
x_62 = lean_array_push(x_53, x_61);
x_63 = lean_st_ref_set(x_51, x_62, x_54);
lean_dec(x_51);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = l_Lake_Job_renew___redArg(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_45);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStderr___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdout___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_withStdin___at___IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildStatic___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_ExternLib_recBuildStatic___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_staticFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_mkRelPathString(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_Json_compress(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_ExternLib_staticFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_ExternLib_staticFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_instDataKindFilePath;
x_3 = l_Lake_ExternLib_keyword;
x_4 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic), 7, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_staticFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_ExternLib_staticFacetConfig_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_ExternLib_staticFacetConfig___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_65; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_65 = l_System_Platform_isOSX;
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_mk_string_unchecked("-Wl,--whole-archive", 19, 19);
x_67 = lean_mk_string_unchecked("-Wl,--no-whole-archive", 22, 22);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_70 = lean_array_push(x_69, x_66);
x_71 = lean_array_push(x_70, x_4);
x_72 = lean_array_push(x_71, x_67);
x_17 = x_72;
goto block_64;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_mk_string_unchecked("-Wl,-force_load,", 16, 16);
x_74 = lean_string_append(x_73, x_4);
lean_dec(x_4);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_mk_empty_array_with_capacity(x_75);
x_77 = lean_array_push(x_76, x_74);
x_17 = x_77;
goto block_64;
}
block_64:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = l_Array_append(lean_box(0), x_17, x_1);
x_19 = l_Array_append(lean_box(0), x_18, x_2);
x_20 = lean_mk_string_unchecked("-L", 2, 2);
x_21 = lean_ctor_get(x_16, 3);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_array_push(x_23, x_20);
x_25 = lean_array_push(x_24, x_21);
x_26 = l_Array_append(lean_box(0), x_19, x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_16, 18);
lean_inc(x_27);
x_28 = l_Array_append(lean_box(0), x_26, x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_16, 12);
lean_inc(x_29);
lean_dec(x_16);
x_30 = l_Lake_compileSharedLib(x_3, x_28, x_29, x_11, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_14);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_13);
lean_ctor_set(x_31, 1, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_14);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_13);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_30, 0, x_40);
return x_30;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_44 = x_31;
} else {
 lean_dec_ref(x_31);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_14);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_13);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_30, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_31, 1);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_14);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_13);
lean_ctor_set(x_31, 1, x_52);
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_31, 0);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_31);
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_14);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_30, 0, x_56);
return x_30;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_30, 1);
lean_inc(x_57);
lean_dec(x_30);
x_58 = lean_ctor_get(x_31, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_60 = x_31;
} else {
 lean_dec_ref(x_31);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_14);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_13);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint64_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = l_Lake_BuildTrace_mix(x_12, x_13);
x_64 = l_Lake_Hash_nil;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_array_get_size(x_1);
x_67 = lean_nat_dec_lt(x_65, x_66);
if (x_67 == 0)
{
lean_dec(x_66);
x_15 = x_64;
goto block_63;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_66, x_66);
if (x_68 == 0)
{
lean_dec(x_66);
x_15 = x_64;
goto block_63;
}
else
{
size_t x_69; size_t x_70; uint64_t x_71; 
x_69 = lean_usize_of_nat(x_65);
x_70 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_71 = l_Array_foldlMUnsafe_fold___at___Lake_buildLeanO_spec__0(x_1, x_69, x_70, x_64);
x_15 = x_71;
goto block_63;
}
}
block_63:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_16 = lean_mk_string_unchecked("pure: ", 6, 6);
x_17 = lean_mk_string_unchecked("#", 1, 1);
lean_inc(x_1);
x_18 = lean_array_to_list(x_1);
x_19 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_16, x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_mk_empty_array_with_capacity(x_22);
x_24 = lean_nat_to_int(x_22);
x_25 = lean_uint32_of_nat(x_22);
x_26 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint32(x_26, sizeof(void*)*1, x_25);
x_27 = lean_box_uint64(x_15);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_26);
x_29 = l_Lake_BuildTrace_mix(x_14, x_28);
x_30 = l_Lake_platformTrace;
x_31 = l_Lake_BuildTrace_mix(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_11);
x_33 = l_Lake_sharedLibExt;
lean_inc(x_3);
x_34 = l_System_FilePath_withExtension(x_3, x_33);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed), 10, 4);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_1);
lean_closure_set(x_35, 2, x_34);
lean_closure_set(x_35, 3, x_3);
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
lean_inc(x_34);
x_38 = l_Lake_buildFileUnlessUpToDate_x27(x_34, x_35, x_37, x_4, x_5, x_6, x_7, x_32, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
lean_ctor_set(x_39, 0, x_34);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_34);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_38, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_39, 0);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_39);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_38, 0, x_56);
return x_38;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_dec(x_38);
x_58 = lean_ctor_get(x_39, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_60 = x_39;
} else {
 lean_dec_ref(x_39);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lake_buildLeanSharedLibOfStatic___lam__1), 9, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lake_Job_mapM___at___Lake_buildLeanO_spec__1___redArg(x_1, x_10, x_11, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_buildLeanSharedLibOfStatic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_buildLeanSharedLibOfStatic___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildShared___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 8);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_mk_string_unchecked("<nil>", 5, 5);
x_20 = l_Lake_BuildTrace_nil(x_19);
x_21 = l_Lake_buildLeanSharedLibOfStatic(x_13, x_16, x_18, x_3, x_4, x_5, x_6, x_20, x_11);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_10, 0, x_23);
lean_ctor_set(x_21, 0, x_10);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_10, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 8);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_mk_string_unchecked("<nil>", 5, 5);
x_35 = l_Lake_BuildTrace_nil(x_34);
x_36 = l_Lake_buildLeanSharedLibOfStatic(x_27, x_31, x_33, x_3, x_4, x_5, x_6, x_35, x_11);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_28);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_9, 0);
lean_dec(x_43);
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_dec(x_9);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_mk_string_unchecked("static", 6, 6);
x_10 = l_Lake_ExternLib_staticFacet;
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_8);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = l_Lake_ExternLib_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_10);
x_16 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildShared___lam__0), 8, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_11);
lean_inc(x_5);
x_17 = l_Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic___lam__1___boxed), 1, 0);
x_23 = l_Lean_Name_str___override(x_8, x_9);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Name_toString(x_23, x_25, x_22);
x_27 = lean_mk_string_unchecked(":shared", 7, 7);
x_28 = lean_ctor_get(x_5, 3);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_st_ref_take(x_28, x_19);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_32);
x_37 = lean_unbox(x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_37);
x_38 = l_Lake_Job_toOpaque___redArg(x_36);
x_39 = lean_array_push(x_30, x_38);
x_40 = lean_st_ref_set(x_28, x_39, x_31);
lean_dec(x_28);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lake_Job_renew___redArg(x_36);
lean_ctor_set(x_18, 0, x_43);
lean_ctor_set(x_40, 0, x_18);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lake_Job_renew___redArg(x_36);
lean_ctor_set(x_18, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
x_49 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic___lam__1___boxed), 1, 0);
x_50 = l_Lean_Name_str___override(x_8, x_9);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
x_53 = l_Lean_Name_toString(x_50, x_52, x_49);
x_54 = lean_mk_string_unchecked(":shared", 7, 7);
x_55 = lean_ctor_get(x_5, 3);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_st_ref_take(x_55, x_19);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_60 = lean_box(0);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_unbox(x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_64);
x_65 = l_Lake_Job_toOpaque___redArg(x_63);
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_st_ref_set(x_55, x_66, x_58);
lean_dec(x_55);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = l_Lake_Job_renew___redArg(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_48);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_ExternLib_staticFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_instDataKindFilePath;
x_3 = l_Lake_ExternLib_keyword;
x_4 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildShared), 7, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_System_FilePath_fileStem(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_mk_string_unchecked("shared library `", 16, 16);
x_10 = lean_string_append(x_9, x_1);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("` has no file name", 18, 18);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_box(3);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
x_18 = lean_array_push(x_16, x_14);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
lean_dec(x_8);
x_25 = l_System_Platform_isWindows;
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_mk_string_unchecked("lib", 3, 3);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_string_utf8_byte_size(x_24);
lean_inc(x_28);
lean_inc(x_24);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Substring_nextn(x_29, x_30, x_27);
lean_dec(x_29);
lean_inc(x_31);
lean_inc(x_24);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_string_utf8_byte_size(x_26);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_Substring_beq(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_24);
x_36 = lean_mk_string_unchecked("shared library `", 16, 16);
x_37 = lean_string_append(x_36, x_1);
lean_dec(x_1);
x_38 = lean_mk_string_unchecked("` does not start with `lib`; this is not supported on Unix", 58, 58);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_box(3);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_unbox(x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
x_43 = lean_ctor_get(x_6, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
x_45 = lean_array_push(x_43, x_41);
x_46 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_dec(x_6);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_46);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_7);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_string_utf8_extract(x_24, x_31, x_28);
lean_dec(x_28);
lean_dec(x_31);
lean_dec(x_24);
x_52 = lean_mk_empty_array_with_capacity(x_27);
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_25);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_6);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_box(0);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_mk_empty_array_with_capacity(x_57);
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_24);
lean_ctor_set(x_59, 2, x_58);
x_60 = lean_unbox(x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_6);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_7);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_alloc_closure((void*)(l_Lake_computeDynlibOfShared___lam__0___boxed), 7, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lake_Job_mapM___at___Lake_buildSharedLib_spec__0(lean_box(0), x_1, x_8, x_9, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_computeDynlibOfShared___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_computeDynlibOfShared___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JobResult_prependLog(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_IO_FS_withIsolatedStreams___at___Lake_ensureJob___at___Lake_ExternLib_recBuildStatic_spec__0_spec__0___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_14 = l_Lake_instDataKindDynlib;
x_15 = lean_array_get_size(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_90 = lean_string_utf8_byte_size(x_38);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_instDecidableEqPos(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
x_94 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_38, x_90, x_91);
x_95 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_38, x_94, x_90);
x_96 = lean_string_utf8_extract(x_38, x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_38);
x_97 = lean_string_append(x_93, x_96);
lean_dec(x_96);
x_98 = lean_box(1);
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
x_100 = lean_unbox(x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_100);
x_101 = lean_box(0);
x_102 = lean_array_push(x_37, x_99);
x_103 = l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__1(x_39, x_101, x_2, x_3, x_4, x_5, x_102, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_103;
goto block_89;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_38);
x_104 = lean_box(0);
x_105 = l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__1(x_39, x_104, x_2, x_3, x_4, x_5, x_37, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = x_105;
goto block_89;
}
block_89:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lake_instDecidableRelPosLt(x_15, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_free_object(x_41);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_40, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
lean_inc(x_45);
x_51 = l_Array_shrink___redArg(x_45, x_15);
x_52 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_53 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__0), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_8);
x_57 = lean_task_map(x_53, x_55, x_54, x_56);
x_58 = lean_ctor_get(x_44, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_14);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_59);
lean_ctor_set(x_41, 1, x_51);
lean_ctor_set(x_41, 0, x_60);
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_40);
lean_inc(x_45);
x_61 = l_Array_shrink___redArg(x_45, x_15);
x_62 = l_Array_extract(lean_box(0), x_45, x_15, x_46);
lean_dec(x_45);
x_63 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__0), 2, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_8);
x_67 = lean_task_map(x_63, x_65, x_64, x_66);
x_68 = lean_ctor_get(x_44, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_44, sizeof(void*)*3);
lean_dec(x_44);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_14);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_69);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_41);
lean_ctor_set(x_71, 1, x_42);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_41, 0);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_41);
x_74 = lean_array_get_size(x_73);
x_75 = l_Lake_instDecidableRelPosLt(x_15, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_42);
lean_dec(x_15);
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_76 = x_40;
} else {
 lean_dec_ref(x_40);
 x_76 = lean_box(0);
}
lean_inc(x_73);
x_77 = l_Array_shrink___redArg(x_73, x_15);
x_78 = l_Array_extract(lean_box(0), x_73, x_15, x_74);
lean_dec(x_73);
x_79 = lean_alloc_closure((void*)(l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__0), 2, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_8);
x_83 = lean_task_map(x_79, x_81, x_80, x_82);
x_84 = lean_ctor_get(x_72, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_72, sizeof(void*)*3);
lean_dec(x_72);
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_14);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_77);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_42);
return x_88;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_11, 1);
lean_inc(x_106);
lean_dec(x_11);
x_16 = x_106;
x_17 = x_12;
goto block_35;
}
block_35:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_16);
x_18 = l_Array_shrink___redArg(x_16, x_15);
x_19 = lean_array_get_size(x_16);
x_20 = l_Array_extract(lean_box(0), x_16, x_15, x_19);
lean_dec(x_16);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_box(0);
x_24 = lean_mk_string_unchecked("<nil>", 5, 5);
x_25 = l_Lake_BuildTrace_nil(x_24);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unbox(x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_task_pure(x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_14);
lean_ctor_set(x_31, 2, x_21);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_13;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recComputeDynlib___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_mk_string_unchecked("<nil>", 5, 5);
x_14 = l_Lake_BuildTrace_nil(x_13);
x_15 = l_Lake_computeDynlibOfShared(x_12, x_2, x_3, x_4, x_5, x_14, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_9, 0, x_17);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_mk_string_unchecked("<nil>", 5, 5);
x_24 = l_Lake_BuildTrace_nil(x_23);
x_25 = l_Lake_computeDynlibOfShared(x_21, x_2, x_3, x_4, x_5, x_24, x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_22);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_8, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_8, 0, x_36);
return x_8;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_dec(x_8);
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_40 = x_9;
} else {
 lean_dec_ref(x_9);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recComputeDynlib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_mk_string_unchecked("static", 6, 6);
x_10 = l_Lake_ExternLib_sharedFacet;
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_8);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = l_Lake_ExternLib_keyword;
x_15 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_10);
x_16 = lean_alloc_closure((void*)(l_Lake_ExternLib_recComputeDynlib___lam__0), 7, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_5);
x_17 = l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic___lam__1___boxed), 1, 0);
x_23 = l_Lean_Name_str___override(x_8, x_9);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Name_toString(x_23, x_25, x_22);
x_27 = lean_mk_string_unchecked(":dynlib", 7, 7);
x_28 = lean_ctor_get(x_5, 3);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_st_ref_take(x_28, x_19);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_32);
x_37 = lean_unbox(x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_37);
x_38 = l_Lake_Job_toOpaque___redArg(x_36);
x_39 = lean_array_push(x_30, x_38);
x_40 = lean_st_ref_set(x_28, x_39, x_31);
lean_dec(x_28);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lake_Job_renew___redArg(x_36);
lean_ctor_set(x_18, 0, x_43);
lean_ctor_set(x_40, 0, x_18);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lake_Job_renew___redArg(x_36);
lean_ctor_set(x_18, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
x_49 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildStatic___lam__1___boxed), 1, 0);
x_50 = l_Lean_Name_str___override(x_8, x_9);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
x_53 = l_Lean_Name_toString(x_50, x_52, x_49);
x_54 = lean_mk_string_unchecked(":dynlib", 7, 7);
x_55 = lean_ctor_get(x_5, 3);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_st_ref_take(x_55, x_19);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_60 = lean_box(0);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_unbox(x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_64);
x_65 = l_Lake_Job_toOpaque___redArg(x_63);
x_66 = lean_array_push(x_57, x_65);
x_67 = lean_st_ref_set(x_55, x_66, x_58);
lean_dec(x_55);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = l_Lake_Job_renew___redArg(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_48);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_ensureJob___at___Lake_ExternLib_recComputeDynlib_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_dynlibFacetConfig_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Json_compress(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacetConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_stdFormat___at___Lake_ExternLib_dynlibFacetConfig_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_ExternLib_dynlibFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_instDataKindDynlib;
x_3 = l_Lake_ExternLib_keyword;
x_4 = lean_alloc_closure((void*)(l_Lake_ExternLib_recComputeDynlib), 7, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_stdFormat___at___Lake_ExternLib_dynlibFacetConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_stdFormat___at___Lake_ExternLib_dynlibFacetConfig_spec__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_ExternLib_dynlibFacetConfig___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_ExternLib_recBuildDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lake_ExternLib_staticFacet;
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lake_ExternLib_keyword;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_8);
x_15 = lean_apply_6(x_2, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacetConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_alloc_closure((void*)(l_Lake_ExternLib_staticFacetConfig___lam__0___boxed), 2, 0);
x_2 = l_Lake_instDataKindFilePath;
x_3 = l_Lake_ExternLib_keyword;
x_4 = lean_alloc_closure((void*)(l_Lake_ExternLib_recBuildDefault), 7, 0);
x_5 = lean_box(1);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_7);
return x_6;
}
}
static lean_object* _init_l_Lake_ExternLib_initFacetConfigs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_box(0);
x_2 = l_Lake_ExternLib_defaultFacet;
x_3 = l_Lake_ExternLib_defaultFacetConfig;
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_2, x_3);
x_5 = l_Lake_ExternLib_staticFacet;
x_6 = l_Lake_ExternLib_staticFacetConfig;
x_7 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_5, x_6);
x_8 = l_Lake_ExternLib_sharedFacet;
x_9 = l_Lake_ExternLib_sharedFacetConfig;
x_10 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_7, x_8, x_9);
x_11 = l_Lake_ExternLib_dynlibFacet;
x_12 = l_Lake_ExternLib_dynlibFacetConfig;
x_13 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_10, x_11, x_12);
return x_13;
}
}
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_ExternLib(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_ExternLib_staticFacetConfig = _init_l_Lake_ExternLib_staticFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_staticFacetConfig);
l_Lake_ExternLib_sharedFacetConfig = _init_l_Lake_ExternLib_sharedFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_sharedFacetConfig);
l_Lake_ExternLib_dynlibFacetConfig = _init_l_Lake_ExternLib_dynlibFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_dynlibFacetConfig);
l_Lake_ExternLib_defaultFacetConfig = _init_l_Lake_ExternLib_defaultFacetConfig();
lean_mark_persistent(l_Lake_ExternLib_defaultFacetConfig);
l_Lake_ExternLib_initFacetConfigs = _init_l_Lake_ExternLib_initFacetConfigs();
lean_mark_persistent(l_Lake_ExternLib_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
