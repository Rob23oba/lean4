// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Lake.Load Lake.Build Lake.Util.MainM Lean.Util.FileSetupInfo
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
uint8_t l_Ord_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instOrdBuildType;
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_ensureJob___at___Lake_Module_recBuildDeps_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSrcPath(lean_object*);
extern lean_object* l_Lake_Module_depsFacet;
lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_setupFile_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_setupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_setupFile___lam__1(uint8_t, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Serve_0__Lake_mkLeanPaths_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
lean_object* l_String_toName(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Serve_0__Lake_mkLeanPaths_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanPath(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
static uint32_t _init_l_Lake_noConfigFileCode() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_invalidConfigEnvVar() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_INVALID_CONFIG", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Serve_0__Lake_mkLeanPaths_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_3 = l_Lake_Workspace_leanPath(x_1);
x_4 = l_Lake_Workspace_leanSrcPath(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_array_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Serve_0__Lake_mkLeanPaths_spec__0(x_6, x_8, x_5);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_array_size(x_10);
x_12 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Serve_0__Lake_mkLeanPaths_spec__0(x_11, x_8, x_10);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Serve_0__Lake_mkLeanPaths_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Serve_0__Lake_mkLeanPaths_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_setupFile_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_String_toName(x_4);
x_7 = l_Lake_Workspace_findModule_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_push(x_2, x_9);
x_2 = x_10;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_setupFile___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_7);
x_10 = l_Lake_ensureJob___at___Lake_Module_recBuildDeps_spec__7(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_st_ref_take(x_15, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_3);
x_22 = l_Lake_Job_toOpaque___redArg(x_21);
x_23 = lean_array_push(x_17, x_22);
x_24 = lean_st_ref_set(x_15, x_23, x_18);
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lake_Job_renew___redArg(x_21);
lean_ctor_set(x_11, 0, x_27);
lean_ctor_set(x_24, 0, x_11);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lake_Job_renew___redArg(x_21);
lean_ctor_set(x_11, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_st_ref_take(x_33, x_12);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_2);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_3);
x_40 = l_Lake_Job_toOpaque___redArg(x_39);
x_41 = lean_array_push(x_35, x_40);
x_42 = lean_st_ref_set(x_33, x_41, x_36);
lean_dec(x_33);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = l_Lake_Job_renew___redArg(x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_32);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
static lean_object* _init_l_Lake_setupFile___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = l_Lake_noConfigFileCode;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_29; lean_object* x_30; lean_object* x_52; uint8_t x_53; 
x_52 = l_Lake_resolvePath(x_2, x_5);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_1, 6);
lean_inc(x_56);
x_57 = l_Lake_realConfigFile(x_56, x_55);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = lean_string_utf8_byte_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_instDecidableEqPos(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
uint8_t x_64; 
lean_free_object(x_57);
x_64 = lean_string_dec_eq(x_59, x_54);
lean_dec(x_59);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_52);
x_65 = lean_mk_string_unchecked("LAKE_INVALID_CONFIG", 19, 19);
x_66 = lean_io_getenv(x_65, x_60);
lean_dec(x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_box(1);
x_70 = l_Lake_OutStream_get(x_69, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_71);
x_74 = l_Lake_AnsiMode_isEnabled(x_71, x_73, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_78 = lean_box(x_77);
x_79 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_79, 0, x_71);
lean_closure_set(x_79, 1, x_78);
lean_closure_set(x_79, 2, x_75);
x_80 = l_Lake_loadWorkspace(x_1, x_79, x_76);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_54);
x_83 = l_Lake_Workspace_findModuleBySrc_x3f(x_54, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_mk_empty_array_with_capacity(x_62);
x_85 = l_List_foldl___at___Lake_setupFile_spec__0(x_81, x_84, x_3);
x_86 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_86, 0, x_54);
lean_closure_set(x_86, 1, x_85);
lean_inc(x_81);
x_87 = l_Lake_Workspace_runFetchM(lean_box(0), x_81, x_86, x_4, x_82);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_io_wait(x_90, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_ctor_get(x_92, 1);
lean_dec(x_96);
x_97 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_81, x_95);
lean_dec(x_81);
x_98 = lean_box(0);
lean_ctor_set(x_92, 1, x_98);
lean_ctor_set(x_92, 0, x_97);
x_99 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_92);
x_100 = l_Lean_Json_compress(x_99);
x_101 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_100, x_93);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_101;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; lean_object* x_116; uint8_t x_117; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = lean_io_error_to_string(x_106);
x_109 = lean_box(1);
x_110 = lean_box(0);
x_111 = lean_box(3);
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_108);
x_113 = lean_unbox(x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_113);
x_114 = lean_unbox(x_109);
x_115 = lean_unbox(x_110);
x_116 = l_Lake_OutStream_logEntry(x_69, x_112, x_114, x_115, x_107);
lean_dec(x_112);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint32_t x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_116, 0);
lean_dec(x_118);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_uint32_of_nat(x_119);
x_121 = lean_box_uint32(x_120);
lean_ctor_set_tag(x_116, 1);
lean_ctor_set(x_116, 0, x_121);
return x_116;
}
else
{
lean_object* x_122; lean_object* x_123; uint32_t x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
lean_dec(x_116);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_uint32_of_nat(x_123);
x_125 = lean_box_uint32(x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_92, 0);
lean_inc(x_127);
lean_dec(x_92);
x_128 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_81, x_127);
lean_dec(x_81);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_130);
x_132 = l_Lean_Json_compress(x_131);
x_133 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_132, x_93);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
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
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint32_t x_152; lean_object* x_153; lean_object* x_154; 
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
lean_dec(x_133);
x_140 = lean_io_error_to_string(x_138);
x_141 = lean_box(1);
x_142 = lean_box(0);
x_143 = lean_box(3);
x_144 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_144, 0, x_140);
x_145 = lean_unbox(x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_145);
x_146 = lean_unbox(x_141);
x_147 = lean_unbox(x_142);
x_148 = l_Lake_OutStream_logEntry(x_69, x_144, x_146, x_147, x_139);
lean_dec(x_144);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_uint32_of_nat(x_151);
x_153 = lean_box_uint32(x_152);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_150;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_92);
lean_dec(x_81);
x_155 = lean_ctor_get(x_91, 1);
lean_inc(x_155);
lean_dec(x_91);
x_156 = lean_mk_string_unchecked("build failed", 12, 12);
x_157 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_6 = x_157;
x_7 = x_155;
goto block_28;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_81);
x_158 = lean_ctor_get(x_87, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_87, 1);
lean_inc(x_159);
lean_dec(x_87);
x_6 = x_158;
x_7 = x_159;
goto block_28;
}
}
else
{
uint8_t x_160; 
lean_dec(x_54);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_83);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_161 = lean_ctor_get(x_83, 0);
x_162 = lean_box(x_64);
x_163 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_163, 0, x_162);
x_164 = lean_mk_string_unchecked("setup (", 7, 7);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
x_166 = lean_box(1);
x_167 = lean_unbox(x_166);
x_168 = l_Lean_Name_toString(x_165, x_167, x_163);
x_169 = lean_string_append(x_164, x_168);
lean_dec(x_168);
x_170 = lean_mk_string_unchecked(")", 1, 1);
x_171 = lean_string_append(x_169, x_170);
lean_dec(x_170);
x_172 = l_Lake_Module_depsFacet;
x_173 = lean_ctor_get(x_161, 2);
lean_inc(x_173);
lean_ctor_set_tag(x_83, 0);
lean_ctor_set(x_83, 0, x_173);
x_174 = l_Lake_Module_keyword;
lean_inc(x_161);
x_175 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_175, 0, x_83);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set(x_175, 2, x_161);
lean_ctor_set(x_175, 3, x_172);
x_176 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_176, 0, x_175);
x_177 = lean_box(x_64);
x_178 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_178, 0, x_176);
lean_closure_set(x_178, 1, x_171);
lean_closure_set(x_178, 2, x_177);
lean_inc(x_81);
x_179 = l_Lake_Workspace_runFetchM(lean_box(0), x_81, x_178, x_4, x_82);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_io_wait(x_182, x_181);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_220 = lean_box(0);
x_221 = lean_ctor_get(x_161, 0);
lean_inc(x_221);
lean_dec(x_161);
x_244 = l_Lake_instOrdBuildType;
x_245 = lean_ctor_get(x_221, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_245, 3);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_248 = lean_ctor_get_uint8(x_247, sizeof(void*)*13);
lean_dec(x_247);
x_249 = lean_ctor_get(x_221, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_ctor_get_uint8(x_250, sizeof(void*)*13);
lean_dec(x_250);
x_252 = lean_box(x_248);
x_253 = lean_box(x_251);
x_254 = l_Ord_instDecidableRelLe___redArg(x_244, x_252, x_253);
if (x_254 == 0)
{
x_222 = x_251;
goto block_243;
}
else
{
x_222 = x_248;
goto block_243;
}
block_219:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_81, x_186);
lean_dec(x_81);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_187;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_190);
x_192 = l_Lean_Json_compress(x_191);
x_193 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_192, x_185);
if (lean_obj_tag(x_193) == 0)
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
return x_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_193);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; 
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 1);
lean_inc(x_199);
lean_dec(x_193);
x_200 = lean_io_error_to_string(x_198);
x_201 = lean_box(1);
x_202 = lean_box(0);
x_203 = lean_box(3);
x_204 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_204, 0, x_200);
x_205 = lean_unbox(x_203);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_205);
x_206 = lean_unbox(x_201);
x_207 = lean_unbox(x_202);
x_208 = l_Lake_OutStream_logEntry(x_69, x_204, x_206, x_207, x_199);
lean_dec(x_204);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint32_t x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_208, 0);
lean_dec(x_210);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_uint32_of_nat(x_211);
x_213 = lean_box_uint32(x_212);
lean_ctor_set_tag(x_208, 1);
lean_ctor_set(x_208, 0, x_213);
return x_208;
}
else
{
lean_object* x_214; lean_object* x_215; uint32_t x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_208, 1);
lean_inc(x_214);
lean_dec(x_208);
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_uint32_of_nat(x_215);
x_217 = lean_box_uint32(x_216);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_214);
return x_218;
}
}
}
block_243:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_223 = l_Lake_BuildType_leanOptions(x_222);
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 3);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 4);
lean_inc(x_228);
lean_dec(x_226);
x_229 = l_Array_append(lean_box(0), x_227, x_228);
lean_dec(x_228);
x_230 = l_Array_append(lean_box(0), x_223, x_229);
lean_dec(x_229);
x_231 = lean_ctor_get(x_221, 2);
lean_inc(x_231);
lean_dec(x_221);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = l_Array_append(lean_box(0), x_230, x_233);
lean_dec(x_233);
x_235 = lean_ctor_get(x_232, 4);
lean_inc(x_235);
lean_dec(x_232);
x_236 = l_Array_append(lean_box(0), x_234, x_235);
lean_dec(x_235);
x_237 = lean_array_get_size(x_236);
x_238 = lean_nat_dec_lt(x_62, x_237);
if (x_238 == 0)
{
lean_dec(x_237);
lean_dec(x_236);
x_188 = x_220;
goto block_219;
}
else
{
uint8_t x_239; 
x_239 = lean_nat_dec_le(x_237, x_237);
if (x_239 == 0)
{
lean_dec(x_237);
lean_dec(x_236);
x_188 = x_220;
goto block_219;
}
else
{
size_t x_240; size_t x_241; lean_object* x_242; 
x_240 = lean_usize_of_nat(x_62);
x_241 = lean_usize_of_nat(x_237);
lean_dec(x_237);
x_242 = l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1(x_236, x_240, x_241, x_220);
lean_dec(x_236);
x_188 = x_242;
goto block_219;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_184);
lean_dec(x_161);
lean_dec(x_81);
x_255 = lean_ctor_get(x_183, 1);
lean_inc(x_255);
lean_dec(x_183);
x_256 = lean_mk_string_unchecked("build failed", 12, 12);
x_257 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_29 = x_257;
x_30 = x_255;
goto block_51;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_161);
lean_dec(x_81);
x_258 = lean_ctor_get(x_179, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_179, 1);
lean_inc(x_259);
lean_dec(x_179);
x_29 = x_258;
x_30 = x_259;
goto block_51;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_260 = lean_ctor_get(x_83, 0);
lean_inc(x_260);
lean_dec(x_83);
x_261 = lean_box(x_64);
x_262 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_262, 0, x_261);
x_263 = lean_mk_string_unchecked("setup (", 7, 7);
x_264 = lean_ctor_get(x_260, 1);
lean_inc(x_264);
x_265 = lean_box(1);
x_266 = lean_unbox(x_265);
x_267 = l_Lean_Name_toString(x_264, x_266, x_262);
x_268 = lean_string_append(x_263, x_267);
lean_dec(x_267);
x_269 = lean_mk_string_unchecked(")", 1, 1);
x_270 = lean_string_append(x_268, x_269);
lean_dec(x_269);
x_271 = l_Lake_Module_depsFacet;
x_272 = lean_ctor_get(x_260, 2);
lean_inc(x_272);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_274 = l_Lake_Module_keyword;
lean_inc(x_260);
x_275 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
lean_ctor_set(x_275, 2, x_260);
lean_ctor_set(x_275, 3, x_271);
x_276 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_276, 0, x_275);
x_277 = lean_box(x_64);
x_278 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_278, 0, x_276);
lean_closure_set(x_278, 1, x_270);
lean_closure_set(x_278, 2, x_277);
lean_inc(x_81);
x_279 = l_Lake_Workspace_runFetchM(lean_box(0), x_81, x_278, x_4, x_82);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_io_wait(x_282, x_281);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
x_316 = lean_box(0);
x_317 = lean_ctor_get(x_260, 0);
lean_inc(x_317);
lean_dec(x_260);
x_340 = l_Lake_instOrdBuildType;
x_341 = lean_ctor_get(x_317, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_341, 3);
lean_inc(x_342);
lean_dec(x_341);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_344 = lean_ctor_get_uint8(x_343, sizeof(void*)*13);
lean_dec(x_343);
x_345 = lean_ctor_get(x_317, 2);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_ctor_get_uint8(x_346, sizeof(void*)*13);
lean_dec(x_346);
x_348 = lean_box(x_344);
x_349 = lean_box(x_347);
x_350 = l_Ord_instDecidableRelLe___redArg(x_340, x_348, x_349);
if (x_350 == 0)
{
x_318 = x_347;
goto block_339;
}
else
{
x_318 = x_344;
goto block_339;
}
block_315:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_81, x_286);
lean_dec(x_81);
if (lean_is_scalar(x_287)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_287;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_290);
x_292 = l_Lean_Json_compress(x_291);
x_293 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_292, x_285);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint32_t x_312; lean_object* x_313; lean_object* x_314; 
x_298 = lean_ctor_get(x_293, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_293, 1);
lean_inc(x_299);
lean_dec(x_293);
x_300 = lean_io_error_to_string(x_298);
x_301 = lean_box(1);
x_302 = lean_box(0);
x_303 = lean_box(3);
x_304 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_304, 0, x_300);
x_305 = lean_unbox(x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*1, x_305);
x_306 = lean_unbox(x_301);
x_307 = lean_unbox(x_302);
x_308 = l_Lake_OutStream_logEntry(x_69, x_304, x_306, x_307, x_299);
lean_dec(x_304);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_310 = x_308;
} else {
 lean_dec_ref(x_308);
 x_310 = lean_box(0);
}
x_311 = lean_unsigned_to_nat(1u);
x_312 = lean_uint32_of_nat(x_311);
x_313 = lean_box_uint32(x_312);
if (lean_is_scalar(x_310)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_310;
 lean_ctor_set_tag(x_314, 1);
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_309);
return x_314;
}
}
block_339:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_319 = l_Lake_BuildType_leanOptions(x_318);
x_320 = lean_ctor_get(x_317, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_320, 3);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 4);
lean_inc(x_324);
lean_dec(x_322);
x_325 = l_Array_append(lean_box(0), x_323, x_324);
lean_dec(x_324);
x_326 = l_Array_append(lean_box(0), x_319, x_325);
lean_dec(x_325);
x_327 = lean_ctor_get(x_317, 2);
lean_inc(x_327);
lean_dec(x_317);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec(x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = l_Array_append(lean_box(0), x_326, x_329);
lean_dec(x_329);
x_331 = lean_ctor_get(x_328, 4);
lean_inc(x_331);
lean_dec(x_328);
x_332 = l_Array_append(lean_box(0), x_330, x_331);
lean_dec(x_331);
x_333 = lean_array_get_size(x_332);
x_334 = lean_nat_dec_lt(x_62, x_333);
if (x_334 == 0)
{
lean_dec(x_333);
lean_dec(x_332);
x_288 = x_316;
goto block_315;
}
else
{
uint8_t x_335; 
x_335 = lean_nat_dec_le(x_333, x_333);
if (x_335 == 0)
{
lean_dec(x_333);
lean_dec(x_332);
x_288 = x_316;
goto block_315;
}
else
{
size_t x_336; size_t x_337; lean_object* x_338; 
x_336 = lean_usize_of_nat(x_62);
x_337 = lean_usize_of_nat(x_333);
lean_dec(x_333);
x_338 = l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1(x_332, x_336, x_337, x_316);
lean_dec(x_332);
x_288 = x_338;
goto block_315;
}
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_284);
lean_dec(x_260);
lean_dec(x_81);
x_351 = lean_ctor_get(x_283, 1);
lean_inc(x_351);
lean_dec(x_283);
x_352 = lean_mk_string_unchecked("build failed", 12, 12);
x_353 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_353, 0, x_352);
x_29 = x_353;
x_30 = x_351;
goto block_51;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_260);
lean_dec(x_81);
x_354 = lean_ctor_get(x_279, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_279, 1);
lean_inc(x_355);
lean_dec(x_279);
x_29 = x_354;
x_30 = x_355;
goto block_51;
}
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_363; uint8_t x_364; lean_object* x_365; uint8_t x_366; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
x_356 = lean_ctor_get(x_80, 1);
lean_inc(x_356);
lean_dec(x_80);
x_357 = lean_mk_string_unchecked("failed to load workspace", 24, 24);
x_358 = lean_box(1);
x_359 = lean_box(0);
x_360 = lean_box(3);
x_361 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_361, 0, x_357);
x_362 = lean_unbox(x_360);
lean_ctor_set_uint8(x_361, sizeof(void*)*1, x_362);
x_363 = lean_unbox(x_358);
x_364 = lean_unbox(x_359);
x_365 = l_Lake_OutStream_logEntry(x_69, x_361, x_363, x_364, x_356);
lean_dec(x_361);
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; uint32_t x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_365, 0);
lean_dec(x_367);
x_368 = lean_unsigned_to_nat(1u);
x_369 = lean_uint32_of_nat(x_368);
x_370 = lean_box_uint32(x_369);
lean_ctor_set_tag(x_365, 1);
lean_ctor_set(x_365, 0, x_370);
return x_365;
}
else
{
lean_object* x_371; lean_object* x_372; uint32_t x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_ctor_get(x_365, 1);
lean_inc(x_371);
lean_dec(x_365);
x_372 = lean_unsigned_to_nat(1u);
x_373 = lean_uint32_of_nat(x_372);
x_374 = lean_box_uint32(x_373);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_371);
return x_375;
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_376 = lean_ctor_get(x_66, 1);
lean_inc(x_376);
lean_dec(x_66);
x_377 = lean_ctor_get(x_67, 0);
lean_inc(x_377);
lean_dec(x_67);
x_378 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_377, x_376);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
x_380 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
x_381 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_380, x_379);
if (lean_obj_tag(x_381) == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; uint32_t x_385; lean_object* x_386; 
x_383 = lean_ctor_get(x_381, 0);
lean_dec(x_383);
x_384 = lean_unsigned_to_nat(1u);
x_385 = lean_uint32_of_nat(x_384);
x_386 = lean_box_uint32(x_385);
lean_ctor_set_tag(x_381, 1);
lean_ctor_set(x_381, 0, x_386);
return x_381;
}
else
{
lean_object* x_387; lean_object* x_388; uint32_t x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_ctor_get(x_381, 1);
lean_inc(x_387);
lean_dec(x_381);
x_388 = lean_unsigned_to_nat(1u);
x_389 = lean_uint32_of_nat(x_388);
x_390 = lean_box_uint32(x_389);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_387);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; lean_object* x_403; uint8_t x_404; 
x_392 = lean_ctor_get(x_381, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_381, 1);
lean_inc(x_393);
lean_dec(x_381);
x_394 = lean_io_error_to_string(x_392);
x_395 = lean_box(1);
x_396 = lean_box(0);
x_397 = lean_box(1);
x_398 = lean_box(3);
x_399 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_399, 0, x_394);
x_400 = lean_unbox(x_398);
lean_ctor_set_uint8(x_399, sizeof(void*)*1, x_400);
x_401 = lean_unbox(x_395);
x_402 = lean_unbox(x_396);
x_403 = l_Lake_OutStream_logEntry(x_397, x_399, x_401, x_402, x_393);
lean_dec(x_399);
x_404 = !lean_is_exclusive(x_403);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; uint32_t x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_403, 0);
lean_dec(x_405);
x_406 = lean_unsigned_to_nat(1u);
x_407 = lean_uint32_of_nat(x_406);
x_408 = lean_box_uint32(x_407);
lean_ctor_set_tag(x_403, 1);
lean_ctor_set(x_403, 0, x_408);
return x_403;
}
else
{
lean_object* x_409; lean_object* x_410; uint32_t x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_403, 1);
lean_inc(x_409);
lean_dec(x_403);
x_410 = lean_unsigned_to_nat(1u);
x_411 = lean_uint32_of_nat(x_410);
x_412 = lean_box_uint32(x_411);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_409);
return x_413;
}
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; uint8_t x_423; uint8_t x_424; lean_object* x_425; uint8_t x_426; 
x_414 = lean_ctor_get(x_378, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 1);
lean_inc(x_415);
lean_dec(x_378);
x_416 = lean_io_error_to_string(x_414);
x_417 = lean_box(1);
x_418 = lean_box(0);
x_419 = lean_box(1);
x_420 = lean_box(3);
x_421 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_421, 0, x_416);
x_422 = lean_unbox(x_420);
lean_ctor_set_uint8(x_421, sizeof(void*)*1, x_422);
x_423 = lean_unbox(x_417);
x_424 = lean_unbox(x_418);
x_425 = l_Lake_OutStream_logEntry(x_419, x_421, x_423, x_424, x_415);
lean_dec(x_421);
x_426 = !lean_is_exclusive(x_425);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; uint32_t x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_425, 0);
lean_dec(x_427);
x_428 = lean_unsigned_to_nat(1u);
x_429 = lean_uint32_of_nat(x_428);
x_430 = lean_box_uint32(x_429);
lean_ctor_set_tag(x_425, 1);
lean_ctor_set(x_425, 0, x_430);
return x_425;
}
else
{
lean_object* x_431; lean_object* x_432; uint32_t x_433; lean_object* x_434; lean_object* x_435; 
x_431 = lean_ctor_get(x_425, 1);
lean_inc(x_431);
lean_dec(x_425);
x_432 = lean_unsigned_to_nat(1u);
x_433 = lean_uint32_of_nat(x_432);
x_434 = lean_box_uint32(x_433);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_431);
return x_435;
}
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
x_436 = lean_ctor_get(x_1, 0);
lean_inc(x_436);
lean_dec(x_1);
x_437 = l_Lake_Env_leanPath(x_436);
x_438 = l_Lake_Env_leanSrcPath(x_436);
x_439 = lean_mk_empty_array_with_capacity(x_62);
x_440 = lean_ctor_get(x_436, 0);
lean_inc(x_440);
lean_dec(x_436);
x_441 = lean_ctor_get(x_440, 4);
lean_inc(x_441);
lean_dec(x_440);
x_442 = lean_unsigned_to_nat(1u);
x_443 = lean_mk_empty_array_with_capacity(x_442);
x_444 = lean_array_push(x_443, x_441);
x_445 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_445, 0, x_437);
lean_ctor_set(x_445, 1, x_438);
lean_ctor_set(x_445, 2, x_439);
lean_ctor_set(x_445, 3, x_444);
x_446 = lean_box(0);
lean_ctor_set(x_52, 1, x_446);
lean_ctor_set(x_52, 0, x_445);
x_447 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_52);
x_448 = l_Lean_Json_compress(x_447);
x_449 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_448, x_60);
if (lean_obj_tag(x_449) == 0)
{
uint8_t x_450; 
x_450 = !lean_is_exclusive(x_449);
if (x_450 == 0)
{
return x_449;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_449, 0);
x_452 = lean_ctor_get(x_449, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_449);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; lean_object* x_465; uint8_t x_466; 
x_454 = lean_ctor_get(x_449, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_449, 1);
lean_inc(x_455);
lean_dec(x_449);
x_456 = lean_io_error_to_string(x_454);
x_457 = lean_box(1);
x_458 = lean_box(0);
x_459 = lean_box(1);
x_460 = lean_box(3);
x_461 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_461, 0, x_456);
x_462 = lean_unbox(x_460);
lean_ctor_set_uint8(x_461, sizeof(void*)*1, x_462);
x_463 = lean_unbox(x_457);
x_464 = lean_unbox(x_458);
x_465 = l_Lake_OutStream_logEntry(x_459, x_461, x_463, x_464, x_455);
lean_dec(x_461);
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
lean_object* x_467; uint32_t x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_465, 0);
lean_dec(x_467);
x_468 = lean_uint32_of_nat(x_442);
x_469 = lean_box_uint32(x_468);
lean_ctor_set_tag(x_465, 1);
lean_ctor_set(x_465, 0, x_469);
return x_465;
}
else
{
lean_object* x_470; uint32_t x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_465, 1);
lean_inc(x_470);
lean_dec(x_465);
x_471 = lean_uint32_of_nat(x_442);
x_472 = lean_box_uint32(x_471);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_470);
return x_473;
}
}
}
}
else
{
lean_object* x_474; 
lean_dec(x_59);
lean_free_object(x_52);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_474 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_474);
return x_57;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_475 = lean_ctor_get(x_57, 0);
x_476 = lean_ctor_get(x_57, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_57);
x_477 = lean_string_utf8_byte_size(x_475);
x_478 = lean_unsigned_to_nat(0u);
x_479 = l_instDecidableEqPos(x_477, x_478);
lean_dec(x_477);
if (x_479 == 0)
{
uint8_t x_480; 
x_480 = lean_string_dec_eq(x_475, x_54);
lean_dec(x_475);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_free_object(x_52);
x_481 = lean_mk_string_unchecked("LAKE_INVALID_CONFIG", 19, 19);
x_482 = lean_io_getenv(x_481, x_476);
lean_dec(x_481);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_box(1);
x_486 = l_Lake_OutStream_get(x_485, x_484);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_487);
x_490 = l_Lake_AnsiMode_isEnabled(x_487, x_489, x_488);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_493 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_494 = lean_box(x_493);
x_495 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_495, 0, x_487);
lean_closure_set(x_495, 1, x_494);
lean_closure_set(x_495, 2, x_491);
x_496 = l_Lake_loadWorkspace(x_1, x_495, x_492);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
lean_inc(x_54);
x_499 = l_Lake_Workspace_findModuleBySrc_x3f(x_54, x_497);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_500 = lean_mk_empty_array_with_capacity(x_478);
x_501 = l_List_foldl___at___Lake_setupFile_spec__0(x_497, x_500, x_3);
x_502 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_502, 0, x_54);
lean_closure_set(x_502, 1, x_501);
lean_inc(x_497);
x_503 = l_Lake_Workspace_runFetchM(lean_box(0), x_497, x_502, x_4, x_498);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = lean_ctor_get(x_504, 0);
lean_inc(x_506);
lean_dec(x_504);
x_507 = lean_io_wait(x_506, x_505);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_ctor_get(x_508, 0);
lean_inc(x_510);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_511 = x_508;
} else {
 lean_dec_ref(x_508);
 x_511 = lean_box(0);
}
x_512 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_497, x_510);
lean_dec(x_497);
x_513 = lean_box(0);
if (lean_is_scalar(x_511)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_511;
}
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
x_515 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_514);
x_516 = l_Lean_Json_compress(x_515);
x_517 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_516, x_509);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_520 = x_517;
} else {
 lean_dec_ref(x_517);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(0, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; uint8_t x_530; uint8_t x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint32_t x_536; lean_object* x_537; lean_object* x_538; 
x_522 = lean_ctor_get(x_517, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_517, 1);
lean_inc(x_523);
lean_dec(x_517);
x_524 = lean_io_error_to_string(x_522);
x_525 = lean_box(1);
x_526 = lean_box(0);
x_527 = lean_box(3);
x_528 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_528, 0, x_524);
x_529 = lean_unbox(x_527);
lean_ctor_set_uint8(x_528, sizeof(void*)*1, x_529);
x_530 = lean_unbox(x_525);
x_531 = lean_unbox(x_526);
x_532 = l_Lake_OutStream_logEntry(x_485, x_528, x_530, x_531, x_523);
lean_dec(x_528);
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_534 = x_532;
} else {
 lean_dec_ref(x_532);
 x_534 = lean_box(0);
}
x_535 = lean_unsigned_to_nat(1u);
x_536 = lean_uint32_of_nat(x_535);
x_537 = lean_box_uint32(x_536);
if (lean_is_scalar(x_534)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_534;
 lean_ctor_set_tag(x_538, 1);
}
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_533);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_508);
lean_dec(x_497);
x_539 = lean_ctor_get(x_507, 1);
lean_inc(x_539);
lean_dec(x_507);
x_540 = lean_mk_string_unchecked("build failed", 12, 12);
x_541 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_541, 0, x_540);
x_6 = x_541;
x_7 = x_539;
goto block_28;
}
}
else
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_497);
x_542 = lean_ctor_get(x_503, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_503, 1);
lean_inc(x_543);
lean_dec(x_503);
x_6 = x_542;
x_7 = x_543;
goto block_28;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_54);
lean_dec(x_3);
x_544 = lean_ctor_get(x_499, 0);
lean_inc(x_544);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 x_545 = x_499;
} else {
 lean_dec_ref(x_499);
 x_545 = lean_box(0);
}
x_546 = lean_box(x_480);
x_547 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_547, 0, x_546);
x_548 = lean_mk_string_unchecked("setup (", 7, 7);
x_549 = lean_ctor_get(x_544, 1);
lean_inc(x_549);
x_550 = lean_box(1);
x_551 = lean_unbox(x_550);
x_552 = l_Lean_Name_toString(x_549, x_551, x_547);
x_553 = lean_string_append(x_548, x_552);
lean_dec(x_552);
x_554 = lean_mk_string_unchecked(")", 1, 1);
x_555 = lean_string_append(x_553, x_554);
lean_dec(x_554);
x_556 = l_Lake_Module_depsFacet;
x_557 = lean_ctor_get(x_544, 2);
lean_inc(x_557);
if (lean_is_scalar(x_545)) {
 x_558 = lean_alloc_ctor(0, 1, 0);
} else {
 x_558 = x_545;
 lean_ctor_set_tag(x_558, 0);
}
lean_ctor_set(x_558, 0, x_557);
x_559 = l_Lake_Module_keyword;
lean_inc(x_544);
x_560 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
lean_ctor_set(x_560, 2, x_544);
lean_ctor_set(x_560, 3, x_556);
x_561 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_561, 0, x_560);
x_562 = lean_box(x_480);
x_563 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_563, 0, x_561);
lean_closure_set(x_563, 1, x_555);
lean_closure_set(x_563, 2, x_562);
lean_inc(x_497);
x_564 = l_Lake_Workspace_runFetchM(lean_box(0), x_497, x_563, x_4, x_498);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = lean_ctor_get(x_565, 0);
lean_inc(x_567);
lean_dec(x_565);
x_568 = lean_io_wait(x_567, x_566);
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; lean_object* x_630; lean_object* x_631; uint8_t x_632; lean_object* x_633; lean_object* x_634; uint8_t x_635; 
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec(x_568);
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_572 = x_569;
} else {
 lean_dec_ref(x_569);
 x_572 = lean_box(0);
}
x_601 = lean_box(0);
x_602 = lean_ctor_get(x_544, 0);
lean_inc(x_602);
lean_dec(x_544);
x_625 = l_Lake_instOrdBuildType;
x_626 = lean_ctor_get(x_602, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_626, 3);
lean_inc(x_627);
lean_dec(x_626);
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
lean_dec(x_627);
x_629 = lean_ctor_get_uint8(x_628, sizeof(void*)*13);
lean_dec(x_628);
x_630 = lean_ctor_get(x_602, 2);
lean_inc(x_630);
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
lean_dec(x_630);
x_632 = lean_ctor_get_uint8(x_631, sizeof(void*)*13);
lean_dec(x_631);
x_633 = lean_box(x_629);
x_634 = lean_box(x_632);
x_635 = l_Ord_instDecidableRelLe___redArg(x_625, x_633, x_634);
if (x_635 == 0)
{
x_603 = x_632;
goto block_624;
}
else
{
x_603 = x_629;
goto block_624;
}
block_600:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_574 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_497, x_571);
lean_dec(x_497);
if (lean_is_scalar(x_572)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_572;
}
lean_ctor_set(x_575, 0, x_574);
lean_ctor_set(x_575, 1, x_573);
x_576 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_575);
x_577 = l_Lean_Json_compress(x_576);
x_578 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_577, x_570);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_581 = x_578;
} else {
 lean_dec_ref(x_578);
 x_581 = lean_box(0);
}
if (lean_is_scalar(x_581)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_581;
}
lean_ctor_set(x_582, 0, x_579);
lean_ctor_set(x_582, 1, x_580);
return x_582;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; uint8_t x_591; uint8_t x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint32_t x_597; lean_object* x_598; lean_object* x_599; 
x_583 = lean_ctor_get(x_578, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_578, 1);
lean_inc(x_584);
lean_dec(x_578);
x_585 = lean_io_error_to_string(x_583);
x_586 = lean_box(1);
x_587 = lean_box(0);
x_588 = lean_box(3);
x_589 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_589, 0, x_585);
x_590 = lean_unbox(x_588);
lean_ctor_set_uint8(x_589, sizeof(void*)*1, x_590);
x_591 = lean_unbox(x_586);
x_592 = lean_unbox(x_587);
x_593 = l_Lake_OutStream_logEntry(x_485, x_589, x_591, x_592, x_584);
lean_dec(x_589);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_595 = x_593;
} else {
 lean_dec_ref(x_593);
 x_595 = lean_box(0);
}
x_596 = lean_unsigned_to_nat(1u);
x_597 = lean_uint32_of_nat(x_596);
x_598 = lean_box_uint32(x_597);
if (lean_is_scalar(x_595)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_595;
 lean_ctor_set_tag(x_599, 1);
}
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_594);
return x_599;
}
}
block_624:
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; 
x_604 = l_Lake_BuildType_leanOptions(x_603);
x_605 = lean_ctor_get(x_602, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_605, 3);
lean_inc(x_606);
lean_dec(x_605);
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
lean_dec(x_606);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 4);
lean_inc(x_609);
lean_dec(x_607);
x_610 = l_Array_append(lean_box(0), x_608, x_609);
lean_dec(x_609);
x_611 = l_Array_append(lean_box(0), x_604, x_610);
lean_dec(x_610);
x_612 = lean_ctor_get(x_602, 2);
lean_inc(x_612);
lean_dec(x_602);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
lean_dec(x_612);
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = l_Array_append(lean_box(0), x_611, x_614);
lean_dec(x_614);
x_616 = lean_ctor_get(x_613, 4);
lean_inc(x_616);
lean_dec(x_613);
x_617 = l_Array_append(lean_box(0), x_615, x_616);
lean_dec(x_616);
x_618 = lean_array_get_size(x_617);
x_619 = lean_nat_dec_lt(x_478, x_618);
if (x_619 == 0)
{
lean_dec(x_618);
lean_dec(x_617);
x_573 = x_601;
goto block_600;
}
else
{
uint8_t x_620; 
x_620 = lean_nat_dec_le(x_618, x_618);
if (x_620 == 0)
{
lean_dec(x_618);
lean_dec(x_617);
x_573 = x_601;
goto block_600;
}
else
{
size_t x_621; size_t x_622; lean_object* x_623; 
x_621 = lean_usize_of_nat(x_478);
x_622 = lean_usize_of_nat(x_618);
lean_dec(x_618);
x_623 = l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1(x_617, x_621, x_622, x_601);
lean_dec(x_617);
x_573 = x_623;
goto block_600;
}
}
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_569);
lean_dec(x_544);
lean_dec(x_497);
x_636 = lean_ctor_get(x_568, 1);
lean_inc(x_636);
lean_dec(x_568);
x_637 = lean_mk_string_unchecked("build failed", 12, 12);
x_638 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_638, 0, x_637);
x_29 = x_638;
x_30 = x_636;
goto block_51;
}
}
else
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_544);
lean_dec(x_497);
x_639 = lean_ctor_get(x_564, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_564, 1);
lean_inc(x_640);
lean_dec(x_564);
x_29 = x_639;
x_30 = x_640;
goto block_51;
}
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; uint8_t x_648; uint8_t x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint32_t x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
x_641 = lean_ctor_get(x_496, 1);
lean_inc(x_641);
lean_dec(x_496);
x_642 = lean_mk_string_unchecked("failed to load workspace", 24, 24);
x_643 = lean_box(1);
x_644 = lean_box(0);
x_645 = lean_box(3);
x_646 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_646, 0, x_642);
x_647 = lean_unbox(x_645);
lean_ctor_set_uint8(x_646, sizeof(void*)*1, x_647);
x_648 = lean_unbox(x_643);
x_649 = lean_unbox(x_644);
x_650 = l_Lake_OutStream_logEntry(x_485, x_646, x_648, x_649, x_641);
lean_dec(x_646);
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 lean_ctor_release(x_650, 1);
 x_652 = x_650;
} else {
 lean_dec_ref(x_650);
 x_652 = lean_box(0);
}
x_653 = lean_unsigned_to_nat(1u);
x_654 = lean_uint32_of_nat(x_653);
x_655 = lean_box_uint32(x_654);
if (lean_is_scalar(x_652)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_652;
 lean_ctor_set_tag(x_656, 1);
}
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_651);
return x_656;
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_657 = lean_ctor_get(x_482, 1);
lean_inc(x_657);
lean_dec(x_482);
x_658 = lean_ctor_get(x_483, 0);
lean_inc(x_658);
lean_dec(x_483);
x_659 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_658, x_657);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; 
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
lean_dec(x_659);
x_661 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
x_662 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_661, x_660);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; uint32_t x_666; lean_object* x_667; lean_object* x_668; 
x_663 = lean_ctor_get(x_662, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 x_664 = x_662;
} else {
 lean_dec_ref(x_662);
 x_664 = lean_box(0);
}
x_665 = lean_unsigned_to_nat(1u);
x_666 = lean_uint32_of_nat(x_665);
x_667 = lean_box_uint32(x_666);
if (lean_is_scalar(x_664)) {
 x_668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_668 = x_664;
 lean_ctor_set_tag(x_668, 1);
}
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_663);
return x_668;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; uint8_t x_678; uint8_t x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint32_t x_684; lean_object* x_685; lean_object* x_686; 
x_669 = lean_ctor_get(x_662, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_662, 1);
lean_inc(x_670);
lean_dec(x_662);
x_671 = lean_io_error_to_string(x_669);
x_672 = lean_box(1);
x_673 = lean_box(0);
x_674 = lean_box(1);
x_675 = lean_box(3);
x_676 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_676, 0, x_671);
x_677 = lean_unbox(x_675);
lean_ctor_set_uint8(x_676, sizeof(void*)*1, x_677);
x_678 = lean_unbox(x_672);
x_679 = lean_unbox(x_673);
x_680 = l_Lake_OutStream_logEntry(x_674, x_676, x_678, x_679, x_670);
lean_dec(x_676);
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_682 = x_680;
} else {
 lean_dec_ref(x_680);
 x_682 = lean_box(0);
}
x_683 = lean_unsigned_to_nat(1u);
x_684 = lean_uint32_of_nat(x_683);
x_685 = lean_box_uint32(x_684);
if (lean_is_scalar(x_682)) {
 x_686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_686 = x_682;
 lean_ctor_set_tag(x_686, 1);
}
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_681);
return x_686;
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; uint8_t x_696; uint8_t x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint32_t x_702; lean_object* x_703; lean_object* x_704; 
x_687 = lean_ctor_get(x_659, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_659, 1);
lean_inc(x_688);
lean_dec(x_659);
x_689 = lean_io_error_to_string(x_687);
x_690 = lean_box(1);
x_691 = lean_box(0);
x_692 = lean_box(1);
x_693 = lean_box(3);
x_694 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_694, 0, x_689);
x_695 = lean_unbox(x_693);
lean_ctor_set_uint8(x_694, sizeof(void*)*1, x_695);
x_696 = lean_unbox(x_690);
x_697 = lean_unbox(x_691);
x_698 = l_Lake_OutStream_logEntry(x_692, x_694, x_696, x_697, x_688);
lean_dec(x_694);
x_699 = lean_ctor_get(x_698, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_698)) {
 lean_ctor_release(x_698, 0);
 lean_ctor_release(x_698, 1);
 x_700 = x_698;
} else {
 lean_dec_ref(x_698);
 x_700 = lean_box(0);
}
x_701 = lean_unsigned_to_nat(1u);
x_702 = lean_uint32_of_nat(x_701);
x_703 = lean_box_uint32(x_702);
if (lean_is_scalar(x_700)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_700;
 lean_ctor_set_tag(x_704, 1);
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_699);
return x_704;
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
x_705 = lean_ctor_get(x_1, 0);
lean_inc(x_705);
lean_dec(x_1);
x_706 = l_Lake_Env_leanPath(x_705);
x_707 = l_Lake_Env_leanSrcPath(x_705);
x_708 = lean_mk_empty_array_with_capacity(x_478);
x_709 = lean_ctor_get(x_705, 0);
lean_inc(x_709);
lean_dec(x_705);
x_710 = lean_ctor_get(x_709, 4);
lean_inc(x_710);
lean_dec(x_709);
x_711 = lean_unsigned_to_nat(1u);
x_712 = lean_mk_empty_array_with_capacity(x_711);
x_713 = lean_array_push(x_712, x_710);
x_714 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_714, 0, x_706);
lean_ctor_set(x_714, 1, x_707);
lean_ctor_set(x_714, 2, x_708);
lean_ctor_set(x_714, 3, x_713);
x_715 = lean_box(0);
lean_ctor_set(x_52, 1, x_715);
lean_ctor_set(x_52, 0, x_714);
x_716 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_52);
x_717 = l_Lean_Json_compress(x_716);
x_718 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_717, x_476);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_721 = x_718;
} else {
 lean_dec_ref(x_718);
 x_721 = lean_box(0);
}
if (lean_is_scalar(x_721)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_721;
}
lean_ctor_set(x_722, 0, x_719);
lean_ctor_set(x_722, 1, x_720);
return x_722;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; uint8_t x_732; uint8_t x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; uint32_t x_737; lean_object* x_738; lean_object* x_739; 
x_723 = lean_ctor_get(x_718, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_718, 1);
lean_inc(x_724);
lean_dec(x_718);
x_725 = lean_io_error_to_string(x_723);
x_726 = lean_box(1);
x_727 = lean_box(0);
x_728 = lean_box(1);
x_729 = lean_box(3);
x_730 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_730, 0, x_725);
x_731 = lean_unbox(x_729);
lean_ctor_set_uint8(x_730, sizeof(void*)*1, x_731);
x_732 = lean_unbox(x_726);
x_733 = lean_unbox(x_727);
x_734 = l_Lake_OutStream_logEntry(x_728, x_730, x_732, x_733, x_724);
lean_dec(x_730);
x_735 = lean_ctor_get(x_734, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_736 = x_734;
} else {
 lean_dec_ref(x_734);
 x_736 = lean_box(0);
}
x_737 = lean_uint32_of_nat(x_711);
x_738 = lean_box_uint32(x_737);
if (lean_is_scalar(x_736)) {
 x_739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_739 = x_736;
 lean_ctor_set_tag(x_739, 1);
}
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_735);
return x_739;
}
}
}
else
{
lean_object* x_740; lean_object* x_741; 
lean_dec(x_475);
lean_free_object(x_52);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_740 = l_Lake_setupFile___boxed__const__1;
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_476);
return x_741;
}
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
x_742 = lean_ctor_get(x_52, 0);
x_743 = lean_ctor_get(x_52, 1);
lean_inc(x_743);
lean_inc(x_742);
lean_dec(x_52);
x_744 = lean_ctor_get(x_1, 6);
lean_inc(x_744);
x_745 = l_Lake_realConfigFile(x_744, x_743);
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_748 = x_745;
} else {
 lean_dec_ref(x_745);
 x_748 = lean_box(0);
}
x_749 = lean_string_utf8_byte_size(x_746);
x_750 = lean_unsigned_to_nat(0u);
x_751 = l_instDecidableEqPos(x_749, x_750);
lean_dec(x_749);
if (x_751 == 0)
{
uint8_t x_752; 
lean_dec(x_748);
x_752 = lean_string_dec_eq(x_746, x_742);
lean_dec(x_746);
if (x_752 == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_mk_string_unchecked("LAKE_INVALID_CONFIG", 19, 19);
x_754 = lean_io_getenv(x_753, x_747);
lean_dec(x_753);
x_755 = lean_ctor_get(x_754, 0);
lean_inc(x_755);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; uint8_t x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_756 = lean_ctor_get(x_754, 1);
lean_inc(x_756);
lean_dec(x_754);
x_757 = lean_box(1);
x_758 = l_Lake_OutStream_get(x_757, x_756);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_759);
x_762 = l_Lake_AnsiMode_isEnabled(x_759, x_761, x_760);
x_763 = lean_ctor_get(x_762, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_762, 1);
lean_inc(x_764);
lean_dec(x_762);
x_765 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_766 = lean_box(x_765);
x_767 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_767, 0, x_759);
lean_closure_set(x_767, 1, x_766);
lean_closure_set(x_767, 2, x_763);
x_768 = l_Lake_loadWorkspace(x_1, x_767, x_764);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
lean_inc(x_742);
x_771 = l_Lake_Workspace_findModuleBySrc_x3f(x_742, x_769);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_772 = lean_mk_empty_array_with_capacity(x_750);
x_773 = l_List_foldl___at___Lake_setupFile_spec__0(x_769, x_772, x_3);
x_774 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_774, 0, x_742);
lean_closure_set(x_774, 1, x_773);
lean_inc(x_769);
x_775 = l_Lake_Workspace_runFetchM(lean_box(0), x_769, x_774, x_4, x_770);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = lean_ctor_get(x_776, 0);
lean_inc(x_778);
lean_dec(x_776);
x_779 = lean_io_wait(x_778, x_777);
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_781 = lean_ctor_get(x_779, 1);
lean_inc(x_781);
lean_dec(x_779);
x_782 = lean_ctor_get(x_780, 0);
lean_inc(x_782);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_783 = x_780;
} else {
 lean_dec_ref(x_780);
 x_783 = lean_box(0);
}
x_784 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_769, x_782);
lean_dec(x_769);
x_785 = lean_box(0);
if (lean_is_scalar(x_783)) {
 x_786 = lean_alloc_ctor(0, 2, 0);
} else {
 x_786 = x_783;
}
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
x_787 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_786);
x_788 = l_Lean_Json_compress(x_787);
x_789 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_788, x_781);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_792 = x_789;
} else {
 lean_dec_ref(x_789);
 x_792 = lean_box(0);
}
if (lean_is_scalar(x_792)) {
 x_793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_793 = x_792;
}
lean_ctor_set(x_793, 0, x_790);
lean_ctor_set(x_793, 1, x_791);
return x_793;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; uint8_t x_802; uint8_t x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; uint32_t x_808; lean_object* x_809; lean_object* x_810; 
x_794 = lean_ctor_get(x_789, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_789, 1);
lean_inc(x_795);
lean_dec(x_789);
x_796 = lean_io_error_to_string(x_794);
x_797 = lean_box(1);
x_798 = lean_box(0);
x_799 = lean_box(3);
x_800 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_800, 0, x_796);
x_801 = lean_unbox(x_799);
lean_ctor_set_uint8(x_800, sizeof(void*)*1, x_801);
x_802 = lean_unbox(x_797);
x_803 = lean_unbox(x_798);
x_804 = l_Lake_OutStream_logEntry(x_757, x_800, x_802, x_803, x_795);
lean_dec(x_800);
x_805 = lean_ctor_get(x_804, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_804)) {
 lean_ctor_release(x_804, 0);
 lean_ctor_release(x_804, 1);
 x_806 = x_804;
} else {
 lean_dec_ref(x_804);
 x_806 = lean_box(0);
}
x_807 = lean_unsigned_to_nat(1u);
x_808 = lean_uint32_of_nat(x_807);
x_809 = lean_box_uint32(x_808);
if (lean_is_scalar(x_806)) {
 x_810 = lean_alloc_ctor(1, 2, 0);
} else {
 x_810 = x_806;
 lean_ctor_set_tag(x_810, 1);
}
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_805);
return x_810;
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_780);
lean_dec(x_769);
x_811 = lean_ctor_get(x_779, 1);
lean_inc(x_811);
lean_dec(x_779);
x_812 = lean_mk_string_unchecked("build failed", 12, 12);
x_813 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_813, 0, x_812);
x_6 = x_813;
x_7 = x_811;
goto block_28;
}
}
else
{
lean_object* x_814; lean_object* x_815; 
lean_dec(x_769);
x_814 = lean_ctor_get(x_775, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_775, 1);
lean_inc(x_815);
lean_dec(x_775);
x_6 = x_814;
x_7 = x_815;
goto block_28;
}
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_742);
lean_dec(x_3);
x_816 = lean_ctor_get(x_771, 0);
lean_inc(x_816);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 x_817 = x_771;
} else {
 lean_dec_ref(x_771);
 x_817 = lean_box(0);
}
x_818 = lean_box(x_752);
x_819 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__1___boxed), 2, 1);
lean_closure_set(x_819, 0, x_818);
x_820 = lean_mk_string_unchecked("setup (", 7, 7);
x_821 = lean_ctor_get(x_816, 1);
lean_inc(x_821);
x_822 = lean_box(1);
x_823 = lean_unbox(x_822);
x_824 = l_Lean_Name_toString(x_821, x_823, x_819);
x_825 = lean_string_append(x_820, x_824);
lean_dec(x_824);
x_826 = lean_mk_string_unchecked(")", 1, 1);
x_827 = lean_string_append(x_825, x_826);
lean_dec(x_826);
x_828 = l_Lake_Module_depsFacet;
x_829 = lean_ctor_get(x_816, 2);
lean_inc(x_829);
if (lean_is_scalar(x_817)) {
 x_830 = lean_alloc_ctor(0, 1, 0);
} else {
 x_830 = x_817;
 lean_ctor_set_tag(x_830, 0);
}
lean_ctor_set(x_830, 0, x_829);
x_831 = l_Lake_Module_keyword;
lean_inc(x_816);
x_832 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
lean_ctor_set(x_832, 2, x_816);
lean_ctor_set(x_832, 3, x_828);
x_833 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__2), 7, 1);
lean_closure_set(x_833, 0, x_832);
x_834 = lean_box(x_752);
x_835 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__3___boxed), 9, 3);
lean_closure_set(x_835, 0, x_833);
lean_closure_set(x_835, 1, x_827);
lean_closure_set(x_835, 2, x_834);
lean_inc(x_769);
x_836 = l_Lake_Workspace_runFetchM(lean_box(0), x_769, x_835, x_4, x_770);
if (lean_obj_tag(x_836) == 0)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
lean_dec(x_836);
x_839 = lean_ctor_get(x_837, 0);
lean_inc(x_839);
lean_dec(x_837);
x_840 = lean_io_wait(x_839, x_838);
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_873; lean_object* x_874; uint8_t x_875; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; uint8_t x_901; lean_object* x_902; lean_object* x_903; uint8_t x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; 
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
lean_dec(x_840);
x_843 = lean_ctor_get(x_841, 0);
lean_inc(x_843);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_844 = x_841;
} else {
 lean_dec_ref(x_841);
 x_844 = lean_box(0);
}
x_873 = lean_box(0);
x_874 = lean_ctor_get(x_816, 0);
lean_inc(x_874);
lean_dec(x_816);
x_897 = l_Lake_instOrdBuildType;
x_898 = lean_ctor_get(x_874, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_898, 3);
lean_inc(x_899);
lean_dec(x_898);
x_900 = lean_ctor_get(x_899, 1);
lean_inc(x_900);
lean_dec(x_899);
x_901 = lean_ctor_get_uint8(x_900, sizeof(void*)*13);
lean_dec(x_900);
x_902 = lean_ctor_get(x_874, 2);
lean_inc(x_902);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
lean_dec(x_902);
x_904 = lean_ctor_get_uint8(x_903, sizeof(void*)*13);
lean_dec(x_903);
x_905 = lean_box(x_901);
x_906 = lean_box(x_904);
x_907 = l_Ord_instDecidableRelLe___redArg(x_897, x_905, x_906);
if (x_907 == 0)
{
x_875 = x_904;
goto block_896;
}
else
{
x_875 = x_901;
goto block_896;
}
block_872:
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_846 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_769, x_843);
lean_dec(x_769);
if (lean_is_scalar(x_844)) {
 x_847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_847 = x_844;
}
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_845);
x_848 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_847);
x_849 = l_Lean_Json_compress(x_848);
x_850 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_849, x_842);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 lean_ctor_release(x_850, 1);
 x_853 = x_850;
} else {
 lean_dec_ref(x_850);
 x_853 = lean_box(0);
}
if (lean_is_scalar(x_853)) {
 x_854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_854 = x_853;
}
lean_ctor_set(x_854, 0, x_851);
lean_ctor_set(x_854, 1, x_852);
return x_854;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; uint8_t x_862; uint8_t x_863; uint8_t x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint32_t x_869; lean_object* x_870; lean_object* x_871; 
x_855 = lean_ctor_get(x_850, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_850, 1);
lean_inc(x_856);
lean_dec(x_850);
x_857 = lean_io_error_to_string(x_855);
x_858 = lean_box(1);
x_859 = lean_box(0);
x_860 = lean_box(3);
x_861 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_861, 0, x_857);
x_862 = lean_unbox(x_860);
lean_ctor_set_uint8(x_861, sizeof(void*)*1, x_862);
x_863 = lean_unbox(x_858);
x_864 = lean_unbox(x_859);
x_865 = l_Lake_OutStream_logEntry(x_757, x_861, x_863, x_864, x_856);
lean_dec(x_861);
x_866 = lean_ctor_get(x_865, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 lean_ctor_release(x_865, 1);
 x_867 = x_865;
} else {
 lean_dec_ref(x_865);
 x_867 = lean_box(0);
}
x_868 = lean_unsigned_to_nat(1u);
x_869 = lean_uint32_of_nat(x_868);
x_870 = lean_box_uint32(x_869);
if (lean_is_scalar(x_867)) {
 x_871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_871 = x_867;
 lean_ctor_set_tag(x_871, 1);
}
lean_ctor_set(x_871, 0, x_870);
lean_ctor_set(x_871, 1, x_866);
return x_871;
}
}
block_896:
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; uint8_t x_891; 
x_876 = l_Lake_BuildType_leanOptions(x_875);
x_877 = lean_ctor_get(x_874, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_877, 3);
lean_inc(x_878);
lean_dec(x_877);
x_879 = lean_ctor_get(x_878, 1);
lean_inc(x_879);
lean_dec(x_878);
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_879, 4);
lean_inc(x_881);
lean_dec(x_879);
x_882 = l_Array_append(lean_box(0), x_880, x_881);
lean_dec(x_881);
x_883 = l_Array_append(lean_box(0), x_876, x_882);
lean_dec(x_882);
x_884 = lean_ctor_get(x_874, 2);
lean_inc(x_884);
lean_dec(x_874);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
lean_dec(x_884);
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = l_Array_append(lean_box(0), x_883, x_886);
lean_dec(x_886);
x_888 = lean_ctor_get(x_885, 4);
lean_inc(x_888);
lean_dec(x_885);
x_889 = l_Array_append(lean_box(0), x_887, x_888);
lean_dec(x_888);
x_890 = lean_array_get_size(x_889);
x_891 = lean_nat_dec_lt(x_750, x_890);
if (x_891 == 0)
{
lean_dec(x_890);
lean_dec(x_889);
x_845 = x_873;
goto block_872;
}
else
{
uint8_t x_892; 
x_892 = lean_nat_dec_le(x_890, x_890);
if (x_892 == 0)
{
lean_dec(x_890);
lean_dec(x_889);
x_845 = x_873;
goto block_872;
}
else
{
size_t x_893; size_t x_894; lean_object* x_895; 
x_893 = lean_usize_of_nat(x_750);
x_894 = lean_usize_of_nat(x_890);
lean_dec(x_890);
x_895 = l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1(x_889, x_893, x_894, x_873);
lean_dec(x_889);
x_845 = x_895;
goto block_872;
}
}
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_841);
lean_dec(x_816);
lean_dec(x_769);
x_908 = lean_ctor_get(x_840, 1);
lean_inc(x_908);
lean_dec(x_840);
x_909 = lean_mk_string_unchecked("build failed", 12, 12);
x_910 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_910, 0, x_909);
x_29 = x_910;
x_30 = x_908;
goto block_51;
}
}
else
{
lean_object* x_911; lean_object* x_912; 
lean_dec(x_816);
lean_dec(x_769);
x_911 = lean_ctor_get(x_836, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_836, 1);
lean_inc(x_912);
lean_dec(x_836);
x_29 = x_911;
x_30 = x_912;
goto block_51;
}
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; uint8_t x_919; uint8_t x_920; uint8_t x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; uint32_t x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_742);
lean_dec(x_4);
lean_dec(x_3);
x_913 = lean_ctor_get(x_768, 1);
lean_inc(x_913);
lean_dec(x_768);
x_914 = lean_mk_string_unchecked("failed to load workspace", 24, 24);
x_915 = lean_box(1);
x_916 = lean_box(0);
x_917 = lean_box(3);
x_918 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_918, 0, x_914);
x_919 = lean_unbox(x_917);
lean_ctor_set_uint8(x_918, sizeof(void*)*1, x_919);
x_920 = lean_unbox(x_915);
x_921 = lean_unbox(x_916);
x_922 = l_Lake_OutStream_logEntry(x_757, x_918, x_920, x_921, x_913);
lean_dec(x_918);
x_923 = lean_ctor_get(x_922, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_924 = x_922;
} else {
 lean_dec_ref(x_922);
 x_924 = lean_box(0);
}
x_925 = lean_unsigned_to_nat(1u);
x_926 = lean_uint32_of_nat(x_925);
x_927 = lean_box_uint32(x_926);
if (lean_is_scalar(x_924)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_924;
 lean_ctor_set_tag(x_928, 1);
}
lean_ctor_set(x_928, 0, x_927);
lean_ctor_set(x_928, 1, x_923);
return x_928;
}
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; 
lean_dec(x_742);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_929 = lean_ctor_get(x_754, 1);
lean_inc(x_929);
lean_dec(x_754);
x_930 = lean_ctor_get(x_755, 0);
lean_inc(x_930);
lean_dec(x_755);
x_931 = l_IO_eprint___at_____private_Init_System_IO_0__IO_eprintAux_spec__0(x_930, x_929);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_932 = lean_ctor_get(x_931, 1);
lean_inc(x_932);
lean_dec(x_931);
x_933 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
x_934 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_933, x_932);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; uint32_t x_938; lean_object* x_939; lean_object* x_940; 
x_935 = lean_ctor_get(x_934, 1);
lean_inc(x_935);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_936 = x_934;
} else {
 lean_dec_ref(x_934);
 x_936 = lean_box(0);
}
x_937 = lean_unsigned_to_nat(1u);
x_938 = lean_uint32_of_nat(x_937);
x_939 = lean_box_uint32(x_938);
if (lean_is_scalar(x_936)) {
 x_940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_940 = x_936;
 lean_ctor_set_tag(x_940, 1);
}
lean_ctor_set(x_940, 0, x_939);
lean_ctor_set(x_940, 1, x_935);
return x_940;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; uint8_t x_949; uint8_t x_950; uint8_t x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; uint32_t x_956; lean_object* x_957; lean_object* x_958; 
x_941 = lean_ctor_get(x_934, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_934, 1);
lean_inc(x_942);
lean_dec(x_934);
x_943 = lean_io_error_to_string(x_941);
x_944 = lean_box(1);
x_945 = lean_box(0);
x_946 = lean_box(1);
x_947 = lean_box(3);
x_948 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_948, 0, x_943);
x_949 = lean_unbox(x_947);
lean_ctor_set_uint8(x_948, sizeof(void*)*1, x_949);
x_950 = lean_unbox(x_944);
x_951 = lean_unbox(x_945);
x_952 = l_Lake_OutStream_logEntry(x_946, x_948, x_950, x_951, x_942);
lean_dec(x_948);
x_953 = lean_ctor_get(x_952, 1);
lean_inc(x_953);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_954 = x_952;
} else {
 lean_dec_ref(x_952);
 x_954 = lean_box(0);
}
x_955 = lean_unsigned_to_nat(1u);
x_956 = lean_uint32_of_nat(x_955);
x_957 = lean_box_uint32(x_956);
if (lean_is_scalar(x_954)) {
 x_958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_958 = x_954;
 lean_ctor_set_tag(x_958, 1);
}
lean_ctor_set(x_958, 0, x_957);
lean_ctor_set(x_958, 1, x_953);
return x_958;
}
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; uint8_t x_967; uint8_t x_968; uint8_t x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; uint32_t x_974; lean_object* x_975; lean_object* x_976; 
x_959 = lean_ctor_get(x_931, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_931, 1);
lean_inc(x_960);
lean_dec(x_931);
x_961 = lean_io_error_to_string(x_959);
x_962 = lean_box(1);
x_963 = lean_box(0);
x_964 = lean_box(1);
x_965 = lean_box(3);
x_966 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_966, 0, x_961);
x_967 = lean_unbox(x_965);
lean_ctor_set_uint8(x_966, sizeof(void*)*1, x_967);
x_968 = lean_unbox(x_962);
x_969 = lean_unbox(x_963);
x_970 = l_Lake_OutStream_logEntry(x_964, x_966, x_968, x_969, x_960);
lean_dec(x_966);
x_971 = lean_ctor_get(x_970, 1);
lean_inc(x_971);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_972 = x_970;
} else {
 lean_dec_ref(x_970);
 x_972 = lean_box(0);
}
x_973 = lean_unsigned_to_nat(1u);
x_974 = lean_uint32_of_nat(x_973);
x_975 = lean_box_uint32(x_974);
if (lean_is_scalar(x_972)) {
 x_976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_976 = x_972;
 lean_ctor_set_tag(x_976, 1);
}
lean_ctor_set(x_976, 0, x_975);
lean_ctor_set(x_976, 1, x_971);
return x_976;
}
}
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_742);
lean_dec(x_4);
lean_dec(x_3);
x_977 = lean_ctor_get(x_1, 0);
lean_inc(x_977);
lean_dec(x_1);
x_978 = l_Lake_Env_leanPath(x_977);
x_979 = l_Lake_Env_leanSrcPath(x_977);
x_980 = lean_mk_empty_array_with_capacity(x_750);
x_981 = lean_ctor_get(x_977, 0);
lean_inc(x_981);
lean_dec(x_977);
x_982 = lean_ctor_get(x_981, 4);
lean_inc(x_982);
lean_dec(x_981);
x_983 = lean_unsigned_to_nat(1u);
x_984 = lean_mk_empty_array_with_capacity(x_983);
x_985 = lean_array_push(x_984, x_982);
x_986 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_986, 0, x_978);
lean_ctor_set(x_986, 1, x_979);
lean_ctor_set(x_986, 2, x_980);
lean_ctor_set(x_986, 3, x_985);
x_987 = lean_box(0);
x_988 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_988, 0, x_986);
lean_ctor_set(x_988, 1, x_987);
x_989 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_988);
x_990 = l_Lean_Json_compress(x_989);
x_991 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_990, x_747);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_994 = x_991;
} else {
 lean_dec_ref(x_991);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_992);
lean_ctor_set(x_995, 1, x_993);
return x_995;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; uint8_t x_1004; uint8_t x_1005; uint8_t x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint32_t x_1010; lean_object* x_1011; lean_object* x_1012; 
x_996 = lean_ctor_get(x_991, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_991, 1);
lean_inc(x_997);
lean_dec(x_991);
x_998 = lean_io_error_to_string(x_996);
x_999 = lean_box(1);
x_1000 = lean_box(0);
x_1001 = lean_box(1);
x_1002 = lean_box(3);
x_1003 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1003, 0, x_998);
x_1004 = lean_unbox(x_1002);
lean_ctor_set_uint8(x_1003, sizeof(void*)*1, x_1004);
x_1005 = lean_unbox(x_999);
x_1006 = lean_unbox(x_1000);
x_1007 = l_Lake_OutStream_logEntry(x_1001, x_1003, x_1005, x_1006, x_997);
lean_dec(x_1003);
x_1008 = lean_ctor_get(x_1007, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1009 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1009 = lean_box(0);
}
x_1010 = lean_uint32_of_nat(x_983);
x_1011 = lean_box_uint32(x_1010);
if (lean_is_scalar(x_1009)) {
 x_1012 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1012 = x_1009;
 lean_ctor_set_tag(x_1012, 1);
}
lean_ctor_set(x_1012, 0, x_1011);
lean_ctor_set(x_1012, 1, x_1008);
return x_1012;
}
}
}
else
{
lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_746);
lean_dec(x_742);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1013 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_748)) {
 x_1014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1014 = x_748;
 lean_ctor_set_tag(x_1014, 1);
}
lean_ctor_set(x_1014, 0, x_1013);
lean_ctor_set(x_1014, 1, x_747);
return x_1014;
}
}
block_28:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_io_error_to_string(x_6);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_box(1);
x_12 = lean_box(3);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_8);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = lean_unbox(x_9);
x_16 = lean_unbox(x_10);
x_17 = l_Lake_OutStream_logEntry(x_11, x_13, x_15, x_16, x_7);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_box_uint32(x_21);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_uint32_of_nat(x_24);
x_26 = lean_box_uint32(x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
block_51:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; 
x_31 = lean_io_error_to_string(x_29);
x_32 = lean_box(1);
x_33 = lean_box(0);
x_34 = lean_box(1);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_31);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_unbox(x_32);
x_39 = lean_unbox(x_33);
x_40 = l_Lake_OutStream_logEntry(x_34, x_36, x_38, x_39, x_30);
lean_dec(x_36);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint32_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_uint32_of_nat(x_43);
x_45 = lean_box_uint32(x_44);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; uint32_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_uint32_of_nat(x_47);
x_49 = lean_box_uint32(x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_setupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___Lake_setupFile_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_setupFile_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_setupFile___lam__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_setupFile___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lake_setupFile___lam__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_4);
x_7 = lean_box(1);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_array_uget(x_1, x_2);
x_11 = lean_unbox(x_8);
x_12 = lean_unbox(x_9);
x_13 = l_Lake_OutStream_logEntry(x_7, x_10, x_11, x_12, x_5);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_14;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_serve(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Lake_loadWorkspace), 3, 1);
lean_closure_set(x_36, 0, x_1);
x_37 = l_Lake_LoggerIO_captureLog___redArg(x_36, x_3);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_array_get_size(x_41);
x_68 = lean_nat_dec_lt(x_66, x_67);
if (x_68 == 0)
{
lean_dec(x_67);
x_43 = x_39;
goto block_65;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_67, x_67);
if (x_69 == 0)
{
lean_dec(x_67);
x_43 = x_39;
goto block_65;
}
else
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = lean_usize_of_nat(x_66);
x_72 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_73 = l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_41, x_71, x_72, x_70, x_39);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_43 = x_74;
goto block_65;
}
}
block_35:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 0, 3);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 0, x_9);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 2, x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 7);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("--server", 8, 8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_array_push(x_17, x_15);
x_19 = l_Array_append(lean_box(0), x_18, x_5);
lean_dec(x_5);
x_20 = l_Array_append(lean_box(0), x_19, x_2);
x_21 = lean_box(0);
x_22 = lean_box(1);
x_23 = lean_box(0);
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_4);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_25);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_26);
x_27 = lean_io_process_spawn(x_24, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_io_process_child_wait(x_8, x_28, x_29);
lean_dec(x_28);
lean_dec(x_8);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_8);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
block_65:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_mk_string_unchecked("warning: package configuration has errors, falling back to plain `lean --server`", 80, 80);
x_45 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_44, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = l_Lake_Env_baseVars(x_47);
x_49 = lean_mk_string_unchecked("LAKE_INVALID_CONFIG", 19, 19);
x_50 = l_Lake_Log_toString(x_41);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_48, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_mk_empty_array_with_capacity(x_54);
x_4 = x_53;
x_5 = x_55;
x_6 = x_46;
goto block_35;
}
else
{
uint8_t x_56; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_42);
lean_dec(x_41);
x_60 = lean_ctor_get(x_40, 0);
lean_inc(x_60);
lean_dec(x_40);
lean_inc(x_60);
x_61 = l_Lake_Workspace_augmentedEnvVars(x_60);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 4);
lean_inc(x_64);
lean_dec(x_63);
x_4 = x_61;
x_5 = x_64;
x_6 = x_43;
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_serve(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lake_Load(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_MainM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FileSetupInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
l_Lake_invalidConfigEnvVar = _init_l_Lake_invalidConfigEnvVar();
lean_mark_persistent(l_Lake_invalidConfigEnvVar);
l_Lake_setupFile___boxed__const__1 = _init_l_Lake_setupFile___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
