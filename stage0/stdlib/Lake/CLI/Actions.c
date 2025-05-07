// Lean compiler output
// Module: Lake.CLI.Actions
// Imports: Lake.Build.Run Lake.Build.Targets Lake.Build.Common Lake.CLI.Build
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
LEAN_EXPORT lean_object* l_Lake_exe___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lake_exe___lam__0(lean_object*);
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
extern lean_object* l_Lake_LeanExe_exeFacet;
LEAN_EXPORT lean_object* l_Lake_Package_lint___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_CliError_toString(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_resolveDriver___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_env(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolveLibTarget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0(lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lint___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0___boxed(lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_buildSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_exe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_env(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_5 = l_Lake_Workspace_augmentedEnvVars(x_3);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 0, 3);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, 0, x_8);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, 1, x_9);
x_10 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, 2, x_10);
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_box(0);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_5);
x_15 = lean_unbox(x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_15);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_16);
x_17 = lean_io_process_spawn(x_14, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_process_child_wait(x_7, x_18, x_19);
lean_dec(x_18);
lean_dec(x_7);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_exe___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lake_LeanExe_exeFacet;
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
x_13 = l_Lake_LeanExe_keyword;
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_1);
lean_ctor_set(x_14, 3, x_8);
x_15 = lean_apply_6(x_2, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_exe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Workspace_findLeanExe_x3f(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_exe___lam__0___boxed), 1, 0);
x_8 = lean_mk_string_unchecked("unknown executable `", 20, 20);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_1, x_10, x_7);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("`", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_alloc_closure((void*)(l_Lake_exe___lam__1), 7, 1);
lean_closure_set(x_19, 0, x_18);
lean_inc(x_4);
x_20 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_19, x_3, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_io_wait(x_23, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_6);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lake_env(x_27, x_2, x_4, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_6, 18);
lean_ctor_set(x_6, 0, x_31);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_6);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_6, 18);
lean_ctor_set(x_6, 0, x_33);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_alloc_closure((void*)(l_Lake_exe___lam__1), 7, 1);
lean_closure_set(x_40, 0, x_39);
lean_inc(x_4);
x_41 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_40, x_3, x_5);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_io_wait(x_44, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lake_env(x_48, x_2, x_4, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_46);
lean_dec(x_4);
lean_dec(x_2);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
x_52 = lean_mk_string_unchecked("build failed", 12, 12);
x_53 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_4);
lean_dec(x_2);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_57 = x_41;
} else {
 lean_dec_ref(x_41);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_exe___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_exe___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_5 = lean_mk_string_unchecked("packing ", 8, 8);
x_6 = lean_string_append(x_5, x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_array_push(x_3, x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 6);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_System_FilePath_normalize(x_13);
x_15 = l_Lake_joinRelative(x_11, x_14);
lean_dec(x_14);
x_16 = lean_box(1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_unbox(x_16);
x_20 = l_Lake_tar(x_15, x_2, x_19, x_18, x_10, x_4);
lean_dec(x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_unpack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_5 = lean_mk_string_unchecked("unpacking ", 10, 10);
x_6 = lean_string_append(x_5, x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_array_push(x_3, x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 6);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_System_FilePath_normalize(x_13);
x_15 = l_Lake_joinRelative(x_11, x_14);
lean_dec(x_14);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lake_untar(x_2, x_15, x_17, x_10, x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_uploadRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = l_Lake_defaultLakeDir;
x_27 = l_Lake_joinRelative(x_25, x_26);
x_28 = lean_ctor_get(x_1, 16);
lean_inc(x_28);
x_29 = l_Lake_joinRelative(x_27, x_28);
lean_inc(x_29);
lean_inc(x_1);
x_30 = l_Lake_Package_pack(x_1, x_29, x_3, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_mk_string_unchecked("uploading ", 10, 10);
x_35 = lean_string_append(x_34, x_2);
x_36 = lean_mk_string_unchecked(":", 1, 1);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_37, x_28);
lean_dec(x_28);
x_39 = lean_box(1);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_41);
x_42 = lean_array_push(x_33, x_40);
x_43 = lean_mk_string_unchecked("release", 7, 7);
x_44 = lean_mk_string_unchecked("upload", 6, 6);
x_45 = lean_mk_string_unchecked("--clobber", 9, 9);
x_46 = lean_unsigned_to_nat(5u);
x_47 = lean_mk_empty_array_with_capacity(x_46);
x_48 = lean_array_push(x_47, x_43);
x_49 = lean_array_push(x_48, x_44);
x_50 = lean_array_push(x_49, x_2);
x_51 = lean_array_push(x_50, x_29);
x_52 = lean_array_push(x_51, x_45);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_ctor_get(x_53, 11);
lean_inc(x_54);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
x_5 = x_52;
x_6 = x_42;
x_7 = x_32;
goto block_24;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked("-R", 2, 2);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_mk_empty_array_with_capacity(x_57);
x_59 = lean_array_push(x_58, x_56);
x_60 = lean_array_push(x_59, x_55);
x_61 = l_Array_append(lean_box(0), x_52, x_60);
lean_dec(x_60);
x_5 = x_61;
x_6 = x_42;
x_7 = x_32;
goto block_24;
}
}
else
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
block_24:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(0, 0, 3);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, 0, x_10);
x_11 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, 1, x_11);
x_12 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, 2, x_12);
x_13 = lean_mk_string_unchecked("gh", 2, 2);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_box(1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_5);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_16);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_20);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*5 + 1, x_21);
x_22 = lean_unbox(x_18);
x_23 = l_Lake_proc(x_19, x_22, x_6, x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = lean_unsigned_to_nat(47u);
x_8 = l_Char_ofNat(x_7);
x_9 = l_instDecidableEqChar(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_utf8_next(x_1, x_3);
x_13 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
lean_inc(x_12);
x_2 = x_12;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_18 = l_List_reverse___redArg(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_resolveDriver___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lake_Package_resolveDriver___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_23 = lean_string_utf8_byte_size(x_3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_instDecidableEqPos(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_String_split___at___Lake_Package_resolveDriver_spec__0(x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_1);
x_9 = x_5;
goto block_22;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_dec(x_30);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_4, 4);
lean_inc(x_37);
x_43 = l_String_toName(x_37);
x_44 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_42, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_40);
lean_free_object(x_26);
x_45 = lean_unbox(x_7);
x_46 = l_Lean_Name_toString(x_6, x_45, x_8);
x_47 = lean_mk_string_unchecked(": unknown ", 10, 10);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_string_append(x_48, x_2);
x_50 = lean_mk_string_unchecked(" driver package '", 17, 17);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_string_append(x_51, x_37);
lean_dec(x_37);
x_53 = lean_mk_string_unchecked("'", 1, 1);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_55);
return x_27;
}
else
{
lean_object* x_56; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_6);
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
lean_dec(x_44);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 1, x_40);
lean_ctor_set(x_27, 0, x_56);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_27);
return x_26;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_27, 0);
lean_inc(x_57);
lean_dec(x_27);
x_58 = lean_ctor_get(x_4, 4);
lean_inc(x_37);
x_59 = l_String_toName(x_37);
x_60 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_58, x_59);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_57);
lean_free_object(x_26);
x_61 = lean_unbox(x_7);
x_62 = l_Lean_Name_toString(x_6, x_61, x_8);
x_63 = lean_mk_string_unchecked(": unknown ", 10, 10);
x_64 = lean_string_append(x_62, x_63);
lean_dec(x_63);
x_65 = lean_string_append(x_64, x_2);
x_66 = lean_mk_string_unchecked(" driver package '", 17, 17);
x_67 = lean_string_append(x_65, x_66);
lean_dec(x_66);
x_68 = lean_string_append(x_67, x_37);
lean_dec(x_37);
x_69 = lean_mk_string_unchecked("'", 1, 1);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_6);
x_73 = lean_ctor_get(x_60, 0);
lean_inc(x_73);
lean_dec(x_60);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_74);
return x_26;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_26, 0);
lean_inc(x_75);
lean_dec(x_26);
x_76 = lean_ctor_get(x_27, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_77 = x_27;
} else {
 lean_dec_ref(x_27);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_4, 4);
lean_inc(x_75);
x_79 = l_String_toName(x_75);
x_80 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_78, x_79);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
x_81 = lean_unbox(x_7);
x_82 = l_Lean_Name_toString(x_6, x_81, x_8);
x_83 = lean_mk_string_unchecked(": unknown ", 10, 10);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = lean_string_append(x_84, x_2);
x_86 = lean_mk_string_unchecked(" driver package '", 17, 17);
x_87 = lean_string_append(x_85, x_86);
lean_dec(x_86);
x_88 = lean_string_append(x_87, x_75);
lean_dec(x_75);
x_89 = lean_mk_string_unchecked("'", 1, 1);
x_90 = lean_string_append(x_88, x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_77)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_77;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_5);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec(x_6);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
lean_dec(x_80);
if (lean_is_scalar(x_77)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_77;
 lean_ctor_set_tag(x_94, 0);
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_76);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_26);
x_9 = x_5;
goto block_22;
}
}
}
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_1);
x_96 = lean_unbox(x_7);
x_97 = l_Lean_Name_toString(x_6, x_96, x_8);
x_98 = lean_mk_string_unchecked(": no ", 5, 5);
x_99 = lean_string_append(x_97, x_98);
lean_dec(x_98);
x_100 = lean_string_append(x_99, x_2);
x_101 = lean_mk_string_unchecked(" driver configured", 18, 18);
x_102 = lean_string_append(x_100, x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_5);
return x_104;
}
block_22:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_unbox(x_7);
x_11 = l_Lean_Name_toString(x_6, x_10, x_8);
x_12 = lean_mk_string_unchecked(": invalid ", 10, 10);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_string_append(x_13, x_2);
x_15 = lean_mk_string_unchecked(" driver '", 9, 9);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_3);
x_18 = lean_mk_string_unchecked("' (too many '/')", 16, 16);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lake_Package_resolveDriver_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_Package_resolveDriver_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lake_Package_resolveDriver_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Package_resolveDriver___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_resolveDriver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Package_resolveDriver(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lake_LeanExe_exeFacet;
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_4);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_apply_6(x_5, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_test(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("test", 4, 4);
x_7 = lean_ctor_get(x_1, 17);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lake_Package_resolveDriver(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_14 = x_9;
} else {
 lean_dec_ref(x_9);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 14);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_12, 13);
lean_inc(x_17);
lean_inc(x_13);
x_18 = l_String_toName(x_13);
x_19 = l_Lean_NameMap_find_x3f(lean_box(0), x_17, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_142; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_closure((void*)(l_Lake_Package_resolveDriver___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_142 = l_Lake_Package_findTargetDecl_x3f(x_18, x_12);
if (lean_obj_tag(x_142) == 0)
{
goto block_141;
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 3);
lean_inc(x_147);
lean_dec(x_144);
x_148 = l_Lake_LeanExe_keyword;
x_149 = lean_name_eq(x_146, x_148);
lean_dec(x_146);
if (x_149 == 0)
{
lean_dec(x_147);
lean_dec(x_145);
lean_free_object(x_142);
goto block_141;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_145);
x_150 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_150, 0, x_12);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set(x_150, 2, x_147);
x_151 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1), 10, 4);
lean_closure_set(x_151, 0, x_20);
lean_closure_set(x_151, 1, x_145);
lean_closure_set(x_151, 2, x_148);
lean_closure_set(x_151, 3, x_150);
lean_inc(x_4);
x_152 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_151, x_3, x_10);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_io_wait(x_155, x_154);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_free_object(x_142);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_array_mk(x_2);
x_161 = l_Array_append(lean_box(0), x_16, x_160);
lean_dec(x_160);
x_162 = l_Lake_env(x_159, x_161, x_4, x_158);
return x_162;
}
else
{
uint8_t x_163; 
lean_dec(x_157);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_156);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_156, 0);
lean_dec(x_164);
x_165 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_142, 18);
lean_ctor_set(x_142, 0, x_165);
lean_ctor_set_tag(x_156, 1);
lean_ctor_set(x_156, 0, x_142);
return x_156;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_156, 1);
lean_inc(x_166);
lean_dec(x_156);
x_167 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_142, 18);
lean_ctor_set(x_142, 0, x_167);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_142);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_free_object(x_142);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_169 = !lean_is_exclusive(x_152);
if (x_169 == 0)
{
return x_152;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_152, 0);
x_171 = lean_ctor_get(x_152, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_152);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_142, 0);
lean_inc(x_173);
lean_dec(x_142);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 3);
lean_inc(x_176);
lean_dec(x_173);
x_177 = l_Lake_LeanExe_keyword;
x_178 = lean_name_eq(x_175, x_177);
lean_dec(x_175);
if (x_178 == 0)
{
lean_dec(x_176);
lean_dec(x_174);
goto block_141;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_174);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_12);
lean_ctor_set(x_179, 1, x_174);
lean_ctor_set(x_179, 2, x_176);
x_180 = lean_alloc_closure((void*)(l_Lake_Package_test___lam__1), 10, 4);
lean_closure_set(x_180, 0, x_20);
lean_closure_set(x_180, 1, x_174);
lean_closure_set(x_180, 2, x_177);
lean_closure_set(x_180, 3, x_179);
lean_inc(x_4);
x_181 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_180, x_3, x_10);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_io_wait(x_184, x_183);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_array_mk(x_2);
x_190 = l_Array_append(lean_box(0), x_16, x_189);
lean_dec(x_189);
x_191 = l_Lake_env(x_188, x_190, x_4, x_187);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_186);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_192 = lean_ctor_get(x_185, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_193 = x_185;
} else {
 lean_dec_ref(x_185);
 x_193 = lean_box(0);
}
x_194 = lean_mk_string_unchecked("build failed", 12, 12);
x_195 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_195, 0, x_194);
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_193;
 lean_ctor_set_tag(x_196, 1);
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_192);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
x_197 = lean_ctor_get(x_181, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_181, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_199 = x_181;
} else {
 lean_dec_ref(x_181);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
}
block_29:
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_unbox(x_21);
x_24 = l_Lean_Name_toString(x_20, x_23, x_22);
x_25 = lean_mk_string_unchecked(": arguments cannot be passed to a library test driver", 53, 53);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
if (lean_is_scalar(x_11)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_11;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
block_39:
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_unbox(x_21);
x_31 = l_Lean_Name_toString(x_20, x_30, x_22);
x_32 = lean_mk_string_unchecked(": invalid test driver: unknown script, executable, or library '", 63, 63);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_33, x_13);
lean_dec(x_13);
x_35 = lean_mk_string_unchecked("'", 1, 1);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_14)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_14;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
block_141:
{
lean_object* x_40; 
x_40 = l_Lake_Package_findTargetDecl_x3f(x_18, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_40) == 0)
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 3);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_46 = l_Lean_Name_mkStr1(x_45);
x_47 = lean_name_eq(x_43, x_46);
lean_dec(x_46);
lean_dec(x_43);
if (x_47 == 0)
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_39;
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
x_48 = l_Array_isEmpty___redArg(x_16);
lean_dec(x_16);
if (x_48 == 0)
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_29;
}
else
{
uint8_t x_49; 
x_49 = l_List_isEmpty___redArg(x_2);
lean_dec(x_2);
if (x_49 == 0)
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
goto block_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_12);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_44);
x_51 = lean_box(0);
x_52 = l_Lake_resolveLibTarget(x_4, x_50, x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_unbox(x_21);
x_56 = l_Lean_Name_toString(x_20, x_55, x_22);
x_57 = lean_mk_string_unchecked(": invalid test driver: ", 23, 23);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = l_Lake_CliError_toString(x_54);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
lean_ctor_set_tag(x_52, 18);
lean_ctor_set(x_52, 0, x_60);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_10);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
lean_dec(x_52);
x_63 = lean_unbox(x_21);
x_64 = l_Lean_Name_toString(x_20, x_63, x_22);
x_65 = lean_mk_string_unchecked(": invalid test driver: ", 23, 23);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = l_Lake_CliError_toString(x_62);
x_68 = lean_string_append(x_66, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_10);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_22);
lean_dec(x_20);
x_71 = !lean_is_exclusive(x_52);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_72 = lean_ctor_get(x_52, 0);
x_73 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 7, 1);
lean_closure_set(x_73, 0, x_72);
x_74 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_77 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_78 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_79 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_80 = lean_box(0);
x_81 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_dec(x_3);
x_82 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_74);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 1, x_75);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 2, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 3, x_77);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 4, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 5, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 6, x_81);
x_83 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_73, x_82, x_10);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_io_wait(x_86, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
lean_dec(x_88);
lean_free_object(x_52);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint32_t x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_87, 0);
lean_dec(x_90);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_uint32_of_nat(x_91);
x_93 = lean_box_uint32(x_92);
lean_ctor_set(x_87, 0, x_93);
return x_87;
}
else
{
lean_object* x_94; lean_object* x_95; uint32_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_uint32_of_nat(x_95);
x_97 = lean_box_uint32(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_88);
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_87, 0);
lean_dec(x_100);
x_101 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_52, 18);
lean_ctor_set(x_52, 0, x_101);
lean_ctor_set_tag(x_87, 1);
lean_ctor_set(x_87, 0, x_52);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_dec(x_87);
x_103 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_52, 18);
lean_ctor_set(x_52, 0, x_103);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_52);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_free_object(x_52);
x_105 = !lean_is_exclusive(x_83);
if (x_105 == 0)
{
return x_83;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_83, 0);
x_107 = lean_ctor_get(x_83, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_83);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_109 = lean_ctor_get(x_52, 0);
lean_inc(x_109);
lean_dec(x_52);
x_110 = lean_alloc_closure((void*)(l_Lake_buildSpecs), 7, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_112 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_113 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_114 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_115 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 4);
x_116 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 5);
x_117 = lean_box(0);
x_118 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 6);
lean_dec(x_3);
x_119 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 1, x_112);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 2, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 3, x_114);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 4, x_115);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 5, x_116);
lean_ctor_set_uint8(x_119, sizeof(void*)*1 + 6, x_118);
x_120 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_110, x_119, x_10);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_io_wait(x_123, x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint32_t x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
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
x_128 = lean_unsigned_to_nat(0u);
x_129 = lean_uint32_of_nat(x_128);
x_130 = lean_box_uint32(x_129);
if (lean_is_scalar(x_127)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_127;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_125);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
 x_133 = lean_box(0);
}
x_134 = lean_mk_string_unchecked("build failed", 12, 12);
x_135 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_135, 0, x_134);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_133;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_120, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_120, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_139 = x_120;
} else {
 lean_dec_ref(x_120);
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
}
}
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_201 = lean_ctor_get(x_19, 0);
lean_inc(x_201);
lean_dec(x_19);
x_202 = lean_array_to_list(x_16);
x_203 = l_List_appendTR(lean_box(0), x_202, x_2);
x_204 = l_Lake_Script_run(x_203, x_201, x_4, x_10);
return x_204;
}
}
else
{
uint8_t x_205; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_8);
if (x_205 == 0)
{
return x_8;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_8, 0);
x_207 = lean_ctor_get(x_8, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_8);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lake_LeanExe_exeFacet;
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_11);
x_15 = lean_apply_6(x_5, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("lint", 4, 4);
x_7 = lean_ctor_get(x_1, 18);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lake_Package_resolveDriver(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 16);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_12, 13);
lean_inc(x_29);
lean_inc(x_13);
x_30 = l_String_toName(x_13);
x_31 = l_Lean_NameMap_find_x3f(lean_box(0), x_29, x_30);
lean_dec(x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = l_Lake_Package_findTargetDecl_x3f(x_30, x_12);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_26;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 3);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lake_LeanExe_keyword;
x_39 = lean_name_eq(x_36, x_38);
lean_dec(x_36);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
lean_free_object(x_32);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_35);
lean_inc(x_12);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_37);
x_41 = lean_alloc_closure((void*)(l_Lake_Package_lint___lam__1___boxed), 10, 4);
lean_closure_set(x_41, 0, x_12);
lean_closure_set(x_41, 1, x_35);
lean_closure_set(x_41, 2, x_38);
lean_closure_set(x_41, 3, x_40);
lean_inc(x_4);
x_42 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_41, x_3, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_io_wait(x_45, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_32);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_array_mk(x_2);
x_51 = l_Array_append(lean_box(0), x_28, x_50);
lean_dec(x_50);
x_52 = l_Lake_env(x_49, x_51, x_4, x_48);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_46, 0);
lean_dec(x_54);
x_55 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_32, 18);
lean_ctor_set(x_32, 0, x_55);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_32);
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_mk_string_unchecked("build failed", 12, 12);
lean_ctor_set_tag(x_32, 18);
lean_ctor_set(x_32, 0, x_57);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_32);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_free_object(x_32);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_42);
if (x_59 == 0)
{
return x_42;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_42, 0);
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_42);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_32, 0);
lean_inc(x_63);
lean_dec(x_32);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 3);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Lake_LeanExe_keyword;
x_68 = lean_name_eq(x_65, x_67);
lean_dec(x_65);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_64);
lean_inc(x_12);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_66);
x_70 = lean_alloc_closure((void*)(l_Lake_Package_lint___lam__1___boxed), 10, 4);
lean_closure_set(x_70, 0, x_12);
lean_closure_set(x_70, 1, x_64);
lean_closure_set(x_70, 2, x_67);
lean_closure_set(x_70, 3, x_69);
lean_inc(x_4);
x_71 = l_Lake_Workspace_runFetchM(lean_box(0), x_4, x_70, x_3, x_10);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_io_wait(x_74, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_mk(x_2);
x_80 = l_Array_append(lean_box(0), x_28, x_79);
lean_dec(x_79);
x_81 = l_Lake_env(x_78, x_80, x_4, x_77);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_2);
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
x_84 = lean_mk_string_unchecked("build failed", 12, 12);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_83;
 lean_ctor_set_tag(x_86, 1);
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_2);
x_87 = lean_ctor_get(x_71, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_89 = x_71;
} else {
 lean_dec_ref(x_71);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_91 = lean_ctor_get(x_31, 0);
lean_inc(x_91);
lean_dec(x_31);
x_92 = lean_array_to_list(x_28);
x_93 = l_List_appendTR(lean_box(0), x_92, x_2);
x_94 = l_Lake_Script_run(x_93, x_91, x_4, x_10);
return x_94;
}
block_26:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Lake_Package_resolveDriver___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_unbox(x_15);
x_18 = l_Lean_Name_toString(x_14, x_17, x_16);
x_19 = lean_mk_string_unchecked(": invalid lint driver: unknown script or executable '", 53, 53);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_13);
lean_dec(x_13);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_11;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
else
{
uint8_t x_95; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_8);
if (x_95 == 0)
{
return x_8;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_8, 0);
x_97 = lean_ctor_get(x_8, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_8);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lint___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Package_lint___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Build(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Run(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Targets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Build(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
