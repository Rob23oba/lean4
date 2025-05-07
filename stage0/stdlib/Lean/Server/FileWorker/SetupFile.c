// Lean compiler output
// Module: Lean.Server.FileWorker.SetupFile
// Imports: Init.System.IO Lean.Server.Utils Lean.Util.FileSetupInfo Lean.Util.LakePath Lean.LoadDynlib Lean.Server.ServerTask
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
lean_object* l_Lean_determineLakePath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___lam__0(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_asTask(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_prefix(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError(lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_load_dynlib(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___lam__0___boxed(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Options_empty;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_io_prim_handle_get_line(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_mk_string_unchecked("", 0, 0);
x_11 = lean_string_dec_eq(x_8, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
lean_inc(x_1);
lean_inc(x_8);
x_12 = lean_apply_2(x_1, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_3 = x_14;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = lean_mk_string_unchecked("", 0, 0);
x_23 = lean_string_dec_eq(x_20, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_1);
lean_inc(x_20);
x_24 = lean_apply_2(x_1, x_20, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_string_append(x_3, x_20);
lean_dec(x_20);
x_3 = x_26;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
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
lean_object* x_32; 
lean_dec(x_20);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile_processStderr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_5 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___lam__0___boxed), 1, 0);
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Name_toString(x_9, x_4, x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_8, x_2, x_10);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; size_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_74 = lean_mk_string_unchecked("setup-file", 10, 10);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_mk_empty_array_with_capacity(x_75);
x_77 = lean_array_push(x_76, x_74);
x_78 = lean_array_push(x_77, x_3);
x_79 = lean_array_size(x_4);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_usize_of_nat(x_80);
x_82 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(x_79, x_81, x_4);
x_83 = l_Array_append(lean_box(0), x_78, x_82);
lean_dec(x_82);
x_84 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_85 = lean_box(x_84);
if (lean_obj_tag(x_85) == 2)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_mk_string_unchecked("--no-build", 10, 10);
x_87 = lean_array_push(x_83, x_86);
x_88 = lean_mk_string_unchecked("--no-cache", 10, 10);
x_89 = lean_array_push(x_87, x_88);
x_7 = x_89;
x_8 = x_6;
goto block_73;
}
else
{
lean_dec(x_85);
x_7 = x_83;
x_8 = x_6;
goto block_73;
}
block_73:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_9 = lean_box(2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 0, 3);
x_12 = lean_unbox(x_9);
lean_ctor_set_uint8(x_11, 0, x_12);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, 1, x_13);
x_14 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, 2, x_14);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_box(1);
x_19 = lean_box(0);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_7);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_21);
x_22 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5 + 1, x_22);
lean_inc(x_20);
x_23 = lean_io_process_spawn(x_20, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_5);
lean_closure_set(x_27, 2, x_7);
lean_closure_set(x_27, 3, x_24);
lean_closure_set(x_27, 4, x_26);
x_28 = l_Lean_Server_ServerTask_IO_asTask(lean_box(0), x_27, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
x_32 = l_IO_FS_Handle_readToEnd(x_31, x_30);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_task_get_own(x_29);
x_36 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_35, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_process_child_wait(x_11, x_24, x_38);
lean_dec(x_24);
lean_dec(x_11);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint32_t x_47; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_string_utf8_byte_size(x_33);
x_43 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_33, x_42, x_16);
x_44 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_33, x_43, x_42);
x_45 = lean_string_utf8_extract(x_33, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_33);
x_46 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_46, 0, x_20);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_37);
x_47 = lean_unbox_uint32(x_41);
lean_dec(x_41);
lean_ctor_set_uint32(x_46, sizeof(void*)*3, x_47);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
x_50 = lean_string_utf8_byte_size(x_33);
x_51 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_33, x_50, x_16);
x_52 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_33, x_51, x_50);
x_53 = lean_string_utf8_extract(x_33, x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_33);
x_54 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_37);
x_55 = lean_unbox_uint32(x_48);
lean_dec(x_48);
lean_ctor_set_uint32(x_54, sizeof(void*)*3, x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_20);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_33);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_11);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
return x_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
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
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_11);
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
return x_32;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_32, 0);
x_67 = lean_ctor_get(x_32, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_32);
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
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_23);
if (x_69 == 0)
{
return x_23;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_23, 0);
x_71 = lean_ctor_get(x_23, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_23);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_box(1);
x_3 = l_Lean_Options_empty;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_box(2);
x_3 = l_Lean_Options_empty;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_Options_empty;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = l_Lean_realPathNormalized(x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
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
else
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_dynlib(x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_System_Uri_fileUriToPath_x3f(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_determineLakePath(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_System_FilePath_pathExists(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_10, x_8, x_2, x_3, x_18);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_41; lean_object* x_42; uint32_t x_43; uint8_t x_44; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_mk_string_unchecked(" ", 1, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_to_list(x_26);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_25);
x_28 = l_String_intercalate(x_23, x_12);
lean_dec(x_23);
x_41 = lean_ctor_get_uint32(x_21, sizeof(void*)*3);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_uint32_of_nat(x_42);
x_44 = lean_uint32_dec_eq(x_41, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_uint32_of_nat(x_45);
x_47 = lean_uint32_dec_eq(x_41, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_uint32_of_nat(x_48);
x_50 = lean_uint32_dec_eq(x_41, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_mk_string_unchecked("`", 1, 1);
x_52 = lean_string_append(x_51, x_28);
lean_dec(x_28);
x_53 = lean_mk_string_unchecked("` failed:\n", 10, 10);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = lean_ctor_get(x_21, 2);
lean_inc(x_59);
lean_dec(x_21);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
x_61 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_60, x_22);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_28);
lean_dec(x_21);
x_62 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_22);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec(x_28);
lean_dec(x_21);
x_63 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_22);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_21, 1);
lean_inc(x_64);
x_65 = l_Lean_Json_parse(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_65);
goto block_40;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26_(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_dec(x_67);
goto block_40;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_28);
lean_dec(x_21);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_get_prefix(x_22);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = l_Lean_initSearchPath(x_70, x_88, x_71);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_ctor_get(x_72, 2);
lean_inc(x_91);
x_92 = lean_array_get_size(x_91);
x_93 = lean_nat_dec_lt(x_42, x_92);
if (x_93 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
x_73 = x_90;
goto block_87;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_92, x_92);
if (x_94 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
x_73 = x_90;
goto block_87;
}
else
{
lean_object* x_95; size_t x_96; size_t x_97; lean_object* x_98; 
x_95 = lean_box(0);
x_96 = lean_usize_of_nat(x_42);
x_97 = lean_usize_of_nat(x_92);
lean_dec(x_92);
x_98 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(x_91, x_96, x_97, x_95, x_90);
lean_dec(x_91);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_73 = x_99;
goto block_87;
}
else
{
uint8_t x_100; 
lean_dec(x_72);
lean_dec(x_68);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
return x_98;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_98);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
block_87:
{
lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 3);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_array_size(x_74);
x_76 = lean_usize_of_nat(x_42);
x_77 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(x_75, x_76, x_74, x_73);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
lean_dec(x_68);
x_81 = l_Lean_LeanOptions_toOptions(x_80);
x_82 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_81, x_78, x_79);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_68);
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_77);
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
uint8_t x_104; 
lean_dec(x_68);
x_104 = !lean_is_exclusive(x_69);
if (x_104 == 0)
{
return x_69;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_69, 0);
x_106 = lean_ctor_get(x_69, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_69);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
block_40:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_mk_string_unchecked("Invalid output from `", 21, 21);
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_mk_string_unchecked("`:\n", 3, 3);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_ctor_get(x_21, 2);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_38, x_22);
return x_39;
}
}
else
{
uint8_t x_108; 
lean_free_object(x_12);
x_108 = !lean_is_exclusive(x_20);
if (x_108 == 0)
{
return x_20;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_20, 0);
x_110 = lean_ctor_get(x_20, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_20);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_12, 1);
lean_inc(x_112);
lean_dec(x_12);
x_113 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_10, x_8, x_2, x_3, x_112);
lean_dec(x_1);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint32_t x_135; lean_object* x_136; uint32_t x_137; uint8_t x_138; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_mk_string_unchecked(" ", 1, 1);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 2);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_array_to_list(x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_String_intercalate(x_116, x_121);
lean_dec(x_116);
x_135 = lean_ctor_get_uint32(x_114, sizeof(void*)*3);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_uint32_of_nat(x_136);
x_138 = lean_uint32_dec_eq(x_135, x_137);
if (x_138 == 0)
{
lean_object* x_139; uint32_t x_140; uint8_t x_141; 
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_uint32_of_nat(x_139);
x_141 = lean_uint32_dec_eq(x_135, x_140);
if (x_141 == 0)
{
lean_object* x_142; uint32_t x_143; uint8_t x_144; 
x_142 = lean_unsigned_to_nat(3u);
x_143 = lean_uint32_of_nat(x_142);
x_144 = lean_uint32_dec_eq(x_135, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_145 = lean_mk_string_unchecked("`", 1, 1);
x_146 = lean_string_append(x_145, x_122);
lean_dec(x_122);
x_147 = lean_mk_string_unchecked("` failed:\n", 10, 10);
x_148 = lean_string_append(x_146, x_147);
lean_dec(x_147);
x_149 = lean_ctor_get(x_114, 1);
lean_inc(x_149);
x_150 = lean_string_append(x_148, x_149);
lean_dec(x_149);
x_151 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
x_152 = lean_string_append(x_150, x_151);
lean_dec(x_151);
x_153 = lean_ctor_get(x_114, 2);
lean_inc(x_153);
lean_dec(x_114);
x_154 = lean_string_append(x_152, x_153);
lean_dec(x_153);
x_155 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_154, x_115);
return x_155;
}
else
{
lean_object* x_156; 
lean_dec(x_122);
lean_dec(x_114);
x_156 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_115);
return x_156;
}
}
else
{
lean_object* x_157; 
lean_dec(x_122);
lean_dec(x_114);
x_157 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_115);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_114, 1);
lean_inc(x_158);
x_159 = l_Lean_Json_parse(x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_dec(x_159);
goto block_134;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26_(x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_dec(x_161);
goto block_134;
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_122);
lean_dec(x_114);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_get_prefix(x_115);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
x_182 = lean_ctor_get(x_166, 0);
lean_inc(x_182);
x_183 = l_Lean_initSearchPath(x_164, x_182, x_165);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_166, 2);
lean_inc(x_185);
x_186 = lean_array_get_size(x_185);
x_187 = lean_nat_dec_lt(x_136, x_186);
if (x_187 == 0)
{
lean_dec(x_186);
lean_dec(x_185);
x_167 = x_184;
goto block_181;
}
else
{
uint8_t x_188; 
x_188 = lean_nat_dec_le(x_186, x_186);
if (x_188 == 0)
{
lean_dec(x_186);
lean_dec(x_185);
x_167 = x_184;
goto block_181;
}
else
{
lean_object* x_189; size_t x_190; size_t x_191; lean_object* x_192; 
x_189 = lean_box(0);
x_190 = lean_usize_of_nat(x_136);
x_191 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_192 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(x_185, x_190, x_191, x_189, x_184);
lean_dec(x_185);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_167 = x_193;
goto block_181;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_166);
lean_dec(x_162);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_196 = x_192;
} else {
 lean_dec_ref(x_192);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
block_181:
{
lean_object* x_168; size_t x_169; size_t x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_166, 3);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_array_size(x_168);
x_170 = lean_usize_of_nat(x_136);
x_171 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(x_169, x_170, x_168, x_167);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_162, 1);
lean_inc(x_174);
lean_dec(x_162);
x_175 = l_Lean_LeanOptions_toOptions(x_174);
x_176 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_175, x_172, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_162);
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_171, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_179 = x_171;
} else {
 lean_dec_ref(x_171);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_162);
x_198 = lean_ctor_get(x_163, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_163, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_200 = x_163;
} else {
 lean_dec_ref(x_163);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
}
block_134:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_123 = lean_mk_string_unchecked("Invalid output from `", 21, 21);
x_124 = lean_string_append(x_123, x_122);
lean_dec(x_122);
x_125 = lean_mk_string_unchecked("`:\n", 3, 3);
x_126 = lean_string_append(x_124, x_125);
lean_dec(x_125);
x_127 = lean_ctor_get(x_114, 1);
lean_inc(x_127);
x_128 = lean_string_append(x_126, x_127);
lean_dec(x_127);
x_129 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
x_130 = lean_string_append(x_128, x_129);
lean_dec(x_129);
x_131 = lean_ctor_get(x_114, 2);
lean_inc(x_131);
lean_dec(x_114);
x_132 = lean_string_append(x_130, x_131);
lean_dec(x_131);
x_133 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_132, x_115);
return x_133;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_113, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_113, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_204 = x_113;
} else {
 lean_dec_ref(x_113);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_9);
if (x_206 == 0)
{
return x_9;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_9, 0);
x_208 = lean_ctor_get(x_9, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_9);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Server_FileWorker_setupFile_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FileSetupInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
