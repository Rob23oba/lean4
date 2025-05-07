// Lean compiler output
// Module: Lake.Config.InstallPath
// Imports: Init.Control.Option Init.Data.Option.Coe Lean.Compiler.FFI Lake.Util.NativeLib Lake.Config.Defaults
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
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanInstall;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_githash;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withInternalCc___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg___lam__0____x40_Lake_Config_InstallPath___hyg_537____boxed(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_nameToSharedLib(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall____x40_Lake_Config_InstallPath___hyg_1116____boxed(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBuildDir;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall___redArg____x40_Lake_Config_InstallPath___hyg_1116____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_findLeanSysroot_x3f_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanSharedLib;
LEAN_EXPORT lean_object* l_Lake_instReprLakeInstall;
extern lean_object* l_System_FilePath_exeExtension;
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall___redArg____x40_Lake_Config_InstallPath___hyg_1116_(lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_findAr(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall____x40_Lake_Config_InstallPath___hyg_537____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanInstall;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___Lake_envToBool_x3f_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprElanInstall;
extern lean_object* l_Lake_sharedLibExt;
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg___lam__0____x40_Lake_Config_InstallPath___hyg_537_(lean_object*);
uint32_t l_Char_toLower(uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg____x40_Lake_Config_InstallPath___hyg_537_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall____x40_Lake_Config_InstallPath___hyg_116_(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_envToBool_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedElanInstall;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall___redArg____x40_Lake_Config_InstallPath___hyg_116____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_setCc(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_findLeanSysroot_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_findLeanSysroot_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initSharedLib;
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withCustomCc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withCustomCc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall____x40_Lake_Config_InstallPath___hyg_116____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall____x40_Lake_Config_InstallPath___hyg_537_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_findLeanSysroot_x3f_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_app_path(lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall____x40_Lake_Config_InstallPath___hyg_1116_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLakeInstall;
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_lakeExe;
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___Lake_envToBool_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withInternalCc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_getGithash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall___redArg____x40_Lake_Config_InstallPath___hyg_116_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
extern lean_object* l_Lake_defaultBinDir;
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
extern lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
extern lean_object* l_Lake_defaultLeanLibDir;
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_envToBool_x3f_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = l_Char_toLower(x_4);
x_6 = lean_string_utf8_set(x_2, x_1, x_5);
x_7 = lean_string_utf8_next(x_6, x_1);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lake_envToBool_x3f_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_dec_eq(x_1, x_5);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_envToBool_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_2 = lean_mk_string_unchecked("y", 1, 1);
x_3 = lean_mk_string_unchecked("yes", 3, 3);
x_4 = lean_mk_string_unchecked("t", 1, 1);
x_5 = lean_mk_string_unchecked("true", 4, 4);
x_6 = lean_mk_string_unchecked("on", 2, 2);
x_7 = lean_mk_string_unchecked("1", 1, 1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_15, x_1);
x_17 = l_List_elem___at___Lake_envToBool_x3f_spec__1(x_16, x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_18 = lean_mk_string_unchecked("n", 1, 1);
x_19 = lean_mk_string_unchecked("no", 2, 2);
x_20 = lean_mk_string_unchecked("f", 1, 1);
x_21 = lean_mk_string_unchecked("false", 5, 5);
x_22 = lean_mk_string_unchecked("off", 3, 3);
x_23 = lean_mk_string_unchecked("0", 1, 1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_elem___at___Lake_envToBool_x3f_spec__1(x_16, x_29);
lean_dec(x_29);
lean_dec(x_16);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(x_17);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_16);
x_34 = lean_box(x_17);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Lake_envToBool_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Lake_envToBool_x3f_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instInhabitedElanInstall() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("", 0, 0);
lean_inc_n(x_1, 3);
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall___redArg____x40_Lake_Config_InstallPath___hyg_116_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("home", 4, 4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_String_quote(x_12);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_13);
lean_inc(x_11);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_mk_string_unchecked(",", 1, 1);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("elan", 4, 4);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_8);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_ctor_get(x_1, 1);
x_35 = l_String_quote(x_34);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_15);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Repr_addAppParen(x_37, x_13);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_unbox(x_21);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_41);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_40);
lean_inc(x_26);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_26);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_28);
x_45 = lean_mk_string_unchecked("binDir", 6, 6);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_8);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_8);
x_49 = lean_unsigned_to_nat(10u);
x_50 = lean_nat_to_int(x_49);
x_51 = lean_ctor_get(x_1, 2);
x_52 = l_String_quote(x_51);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_15);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_15);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Repr_addAppParen(x_54, x_13);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_unbox(x_21);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_26);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_28);
x_62 = lean_mk_string_unchecked("toolchainsDir", 13, 13);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
x_66 = lean_unsigned_to_nat(17u);
x_67 = lean_nat_to_int(x_66);
x_68 = lean_ctor_get(x_1, 3);
x_69 = l_String_quote(x_68);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_15);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Repr_addAppParen(x_71, x_13);
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_unbox(x_21);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_75);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_mk_string_unchecked(" }", 2, 2);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_to_int(x_78);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_2);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_unbox(x_21);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_86);
return x_85;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall____x40_Lake_Config_InstallPath___hyg_116_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall___redArg____x40_Lake_Config_InstallPath___hyg_116_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall___redArg____x40_Lake_Config_InstallPath___hyg_116____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall___redArg____x40_Lake_Config_InstallPath___hyg_116_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall____x40_Lake_Config_InstallPath___hyg_116____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall____x40_Lake_Config_InstallPath___hyg_116_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprElanInstall() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_InstallPath_0__Lake_reprElanInstall____x40_Lake_Config_InstallPath___hyg_116____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_leanExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("bin", 3, 3);
x_3 = l_System_FilePath_join(x_1, x_2);
lean_dec(x_2);
x_4 = lean_mk_string_unchecked("lean", 4, 4);
x_5 = l_System_FilePath_join(x_3, x_4);
lean_dec(x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_leancExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("bin", 3, 3);
x_3 = l_System_FilePath_join(x_1, x_2);
lean_dec(x_2);
x_4 = lean_mk_string_unchecked("leanc", 5, 5);
x_5 = l_System_FilePath_join(x_3, x_4);
lean_dec(x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_leanArExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("bin", 3, 3);
x_3 = l_System_FilePath_join(x_1, x_2);
lean_dec(x_2);
x_4 = lean_mk_string_unchecked("llvm-ar", 7, 7);
x_5 = l_System_FilePath_join(x_3, x_4);
lean_dec(x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_leanCcExe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("bin", 3, 3);
x_3 = l_System_FilePath_join(x_1, x_2);
lean_dec(x_2);
x_4 = lean_mk_string_unchecked("clang", 5, 5);
x_5 = l_System_FilePath_join(x_3, x_4);
lean_dec(x_4);
x_6 = l_System_FilePath_exeExtension;
x_7 = l_System_FilePath_addExtension(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_leanSharedLibDir(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("lib", 3, 3);
x_4 = l_System_FilePath_join(x_1, x_3);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("lean", 4, 4);
x_6 = l_System_FilePath_join(x_4, x_5);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_string_unchecked("bin", 3, 3);
x_8 = l_System_FilePath_join(x_1, x_7);
lean_dec(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lake_leanSharedLib() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("libleanshared", 13, 13);
x_2 = l_Lake_sharedLibExt;
x_3 = l_System_FilePath_addExtension(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_initSharedLib() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("libInit_shared", 14, 14);
x_2 = l_Lake_sharedLibExt;
x_3 = l_System_FilePath_addExtension(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanInstall() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_box(0);
x_3 = l_Array_empty(lean_box(0));
lean_inc_n(x_3, 5);
lean_inc_n(x_1, 12);
x_4 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_1);
lean_ctor_set(x_4, 5, x_1);
lean_ctor_set(x_4, 6, x_1);
lean_ctor_set(x_4, 7, x_1);
lean_ctor_set(x_4, 8, x_1);
lean_ctor_set(x_4, 9, x_1);
lean_ctor_set(x_4, 10, x_1);
lean_ctor_set(x_4, 11, x_1);
lean_ctor_set(x_4, 12, x_1);
lean_ctor_set(x_4, 13, x_3);
lean_ctor_set(x_4, 14, x_3);
lean_ctor_set(x_4, 15, x_3);
lean_ctor_set(x_4, 16, x_3);
lean_ctor_set(x_4, 17, x_3);
lean_ctor_set(x_4, 18, x_3);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*19, x_5);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg___lam__0____x40_Lake_Config_InstallPath___hyg_537_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_quote(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg____x40_Lake_Config_InstallPath___hyg_537_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_80; lean_object* x_81; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_441; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg___lam__0____x40_Lake_Config_InstallPath___hyg_537____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("{ ", 2, 2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("sysroot", 7, 7);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked(" := ", 4, 4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(11u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_String_quote(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_16);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Repr_addAppParen(x_19, x_14);
lean_inc(x_12);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_21);
x_42 = lean_unbox(x_22);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_mk_string_unchecked(",", 1, 1);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_inc(x_45);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(1);
x_177 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_177, 0, x_46);
lean_ctor_set(x_177, 1, x_47);
x_178 = lean_mk_string_unchecked("githash", 7, 7);
x_179 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_9);
x_181 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_9);
x_182 = lean_ctor_get(x_1, 1);
lean_inc(x_182);
x_183 = l_String_quote(x_182);
lean_dec(x_182);
x_184 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_inc(x_12);
x_185 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_185, 0, x_12);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_186, 0, x_185);
x_187 = lean_unbox(x_22);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_187);
x_188 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_186);
lean_inc(x_45);
x_189 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_45);
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_47);
x_191 = lean_mk_string_unchecked("srcDir", 6, 6);
x_192 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_192);
lean_inc(x_9);
x_194 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_9);
x_195 = lean_unsigned_to_nat(10u);
x_196 = lean_nat_to_int(x_195);
x_230 = lean_ctor_get(x_1, 2);
lean_inc(x_230);
x_231 = l_String_quote(x_230);
lean_dec(x_230);
x_232 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_232, 0, x_231);
lean_inc(x_16);
x_233 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_233, 0, x_16);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Repr_addAppParen(x_233, x_14);
lean_inc(x_196);
x_235 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_235, 0, x_196);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_236, 0, x_235);
x_237 = lean_unbox(x_22);
lean_ctor_set_uint8(x_236, sizeof(void*)*1, x_237);
x_238 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_238, 0, x_194);
lean_ctor_set(x_238, 1, x_236);
lean_inc(x_45);
x_239 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_45);
x_240 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_47);
x_241 = lean_mk_string_unchecked("leanLibDir", 10, 10);
x_242 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_243 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
lean_inc(x_9);
x_244 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_9);
x_245 = lean_unsigned_to_nat(14u);
x_246 = lean_nat_to_int(x_245);
x_247 = lean_ctor_get(x_1, 3);
lean_inc(x_247);
x_248 = l_String_quote(x_247);
lean_dec(x_247);
x_249 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_249, 0, x_248);
lean_inc(x_16);
x_250 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_250, 0, x_16);
lean_ctor_set(x_250, 1, x_249);
x_251 = l_Repr_addAppParen(x_250, x_14);
lean_inc(x_246);
x_252 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_253, 0, x_252);
x_254 = lean_unbox(x_22);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_254);
x_255 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_255, 0, x_244);
lean_ctor_set(x_255, 1, x_253);
lean_inc(x_45);
x_256 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_45);
x_257 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_47);
x_258 = lean_mk_string_unchecked("includeDir", 10, 10);
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_259);
lean_inc(x_9);
x_261 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_9);
x_262 = lean_ctor_get(x_1, 4);
lean_inc(x_262);
x_263 = l_String_quote(x_262);
lean_dec(x_262);
x_264 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_264, 0, x_263);
lean_inc(x_16);
x_265 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_265, 0, x_16);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Repr_addAppParen(x_265, x_14);
x_267 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_267, 0, x_246);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_268, 0, x_267);
x_269 = lean_unbox(x_22);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_269);
x_270 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_270, 0, x_261);
lean_ctor_set(x_270, 1, x_268);
lean_inc(x_45);
x_271 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_45);
x_272 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_47);
x_273 = lean_mk_string_unchecked("systemLibDir", 12, 12);
x_274 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_274);
lean_inc(x_9);
x_276 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_9);
x_277 = lean_unsigned_to_nat(16u);
x_278 = lean_nat_to_int(x_277);
x_279 = lean_ctor_get(x_1, 5);
lean_inc(x_279);
x_280 = l_String_quote(x_279);
lean_dec(x_279);
x_281 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_281, 0, x_280);
lean_inc(x_16);
x_282 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_282, 0, x_16);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Repr_addAppParen(x_282, x_14);
x_284 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_284, 0, x_278);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_285, 0, x_284);
x_286 = lean_unbox(x_22);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_286);
x_287 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_287, 0, x_276);
lean_ctor_set(x_287, 1, x_285);
lean_inc(x_45);
x_288 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_45);
x_289 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_47);
x_290 = lean_mk_string_unchecked("binDir", 6, 6);
x_291 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_291);
lean_inc(x_9);
x_293 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_9);
x_294 = lean_ctor_get(x_1, 6);
lean_inc(x_294);
x_295 = l_String_quote(x_294);
lean_dec(x_294);
x_296 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_296, 0, x_295);
lean_inc(x_16);
x_297 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_297, 0, x_16);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_Repr_addAppParen(x_297, x_14);
lean_inc(x_196);
x_299 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_299, 0, x_196);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_300, 0, x_299);
x_301 = lean_unbox(x_22);
lean_ctor_set_uint8(x_300, sizeof(void*)*1, x_301);
x_302 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_302, 0, x_293);
lean_ctor_set(x_302, 1, x_300);
lean_inc(x_45);
x_303 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_45);
x_304 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_47);
x_305 = lean_mk_string_unchecked("lean", 4, 4);
x_306 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_307 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_306);
lean_inc(x_9);
x_308 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_9);
x_309 = lean_unsigned_to_nat(8u);
x_310 = lean_nat_to_int(x_309);
x_311 = lean_ctor_get(x_1, 7);
lean_inc(x_311);
x_312 = l_String_quote(x_311);
lean_dec(x_311);
x_313 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_313, 0, x_312);
lean_inc(x_16);
x_314 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_314, 0, x_16);
lean_ctor_set(x_314, 1, x_313);
x_315 = l_Repr_addAppParen(x_314, x_14);
x_316 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_316, 0, x_310);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_unbox(x_22);
lean_ctor_set_uint8(x_317, sizeof(void*)*1, x_318);
x_319 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_319, 0, x_308);
lean_ctor_set(x_319, 1, x_317);
lean_inc(x_45);
x_320 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_45);
x_321 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_47);
x_322 = lean_mk_string_unchecked("leanc", 5, 5);
x_323 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_324 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_323);
lean_inc(x_9);
x_325 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_9);
x_326 = lean_unsigned_to_nat(9u);
x_327 = lean_nat_to_int(x_326);
x_328 = lean_ctor_get(x_1, 8);
lean_inc(x_328);
x_329 = l_String_quote(x_328);
lean_dec(x_328);
x_330 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_330, 0, x_329);
lean_inc(x_16);
x_331 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_331, 0, x_16);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Repr_addAppParen(x_331, x_14);
x_333 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_333, 0, x_327);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_334, 0, x_333);
x_335 = lean_unbox(x_22);
lean_ctor_set_uint8(x_334, sizeof(void*)*1, x_335);
x_336 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_336, 0, x_325);
lean_ctor_set(x_336, 1, x_334);
lean_inc(x_45);
x_337 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_45);
x_338 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_47);
x_339 = lean_mk_string_unchecked("sharedLib", 9, 9);
x_340 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_340, 0, x_339);
x_341 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_340);
lean_inc(x_9);
x_342 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_9);
x_343 = lean_unsigned_to_nat(13u);
x_344 = lean_nat_to_int(x_343);
x_345 = lean_ctor_get(x_1, 9);
lean_inc(x_345);
x_346 = l_String_quote(x_345);
lean_dec(x_345);
x_347 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_347, 0, x_346);
lean_inc(x_16);
x_348 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_348, 0, x_16);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Repr_addAppParen(x_348, x_14);
x_350 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_350, 0, x_344);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_351, 0, x_350);
x_352 = lean_unbox(x_22);
lean_ctor_set_uint8(x_351, sizeof(void*)*1, x_352);
x_353 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_353, 0, x_342);
lean_ctor_set(x_353, 1, x_351);
lean_inc(x_45);
x_354 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_45);
x_355 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_47);
x_356 = lean_mk_string_unchecked("initSharedLib", 13, 13);
x_357 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_357, 0, x_356);
x_358 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_357);
lean_inc(x_9);
x_359 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_9);
x_360 = lean_unsigned_to_nat(17u);
x_361 = lean_nat_to_int(x_360);
x_362 = lean_ctor_get(x_1, 10);
lean_inc(x_362);
x_363 = l_String_quote(x_362);
lean_dec(x_362);
x_364 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_364, 0, x_363);
lean_inc(x_16);
x_365 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_365, 0, x_16);
lean_ctor_set(x_365, 1, x_364);
x_366 = l_Repr_addAppParen(x_365, x_14);
x_367 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_367, 0, x_361);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_368, 0, x_367);
x_369 = lean_unbox(x_22);
lean_ctor_set_uint8(x_368, sizeof(void*)*1, x_369);
x_370 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_370, 0, x_359);
lean_ctor_set(x_370, 1, x_368);
lean_inc(x_45);
x_371 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_45);
x_372 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_47);
x_373 = lean_mk_string_unchecked("ar", 2, 2);
x_374 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_374, 0, x_373);
x_375 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_374);
lean_inc(x_9);
x_376 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_9);
x_377 = lean_unsigned_to_nat(6u);
x_378 = lean_nat_to_int(x_377);
x_379 = lean_ctor_get(x_1, 11);
lean_inc(x_379);
x_380 = l_String_quote(x_379);
lean_dec(x_379);
x_381 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_381, 0, x_380);
lean_inc(x_16);
x_382 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_382, 0, x_16);
lean_ctor_set(x_382, 1, x_381);
x_383 = l_Repr_addAppParen(x_382, x_14);
lean_inc(x_378);
x_384 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_384, 0, x_378);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_385, 0, x_384);
x_386 = lean_unbox(x_22);
lean_ctor_set_uint8(x_385, sizeof(void*)*1, x_386);
x_387 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_387, 0, x_376);
lean_ctor_set(x_387, 1, x_385);
lean_inc(x_45);
x_388 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_45);
x_389 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_47);
x_390 = lean_mk_string_unchecked("cc", 2, 2);
x_391 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_391, 0, x_390);
x_392 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_391);
lean_inc(x_9);
x_393 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_9);
x_394 = lean_ctor_get(x_1, 12);
lean_inc(x_394);
x_395 = l_String_quote(x_394);
lean_dec(x_394);
x_396 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_396, 0, x_395);
x_397 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_397, 0, x_16);
lean_ctor_set(x_397, 1, x_396);
x_398 = l_Repr_addAppParen(x_397, x_14);
x_399 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_399, 0, x_378);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_400, 0, x_399);
x_401 = lean_unbox(x_22);
lean_ctor_set_uint8(x_400, sizeof(void*)*1, x_401);
x_402 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_402, 0, x_393);
lean_ctor_set(x_402, 1, x_400);
lean_inc(x_45);
x_403 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_45);
x_404 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_47);
x_405 = lean_mk_string_unchecked("customCc", 8, 8);
x_406 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_406);
lean_inc(x_9);
x_408 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_9);
x_409 = lean_unsigned_to_nat(12u);
x_410 = lean_nat_to_int(x_409);
x_441 = lean_ctor_get_uint8(x_1, sizeof(void*)*19);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_mk_string_unchecked("false", 5, 5);
x_443 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_443, 0, x_442);
x_411 = x_443;
goto block_440;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_mk_string_unchecked("true", 4, 4);
x_445 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_445, 0, x_444);
x_411 = x_445;
goto block_440;
}
block_40:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_unbox(x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_mk_string_unchecked(" }", 2, 2);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_to_int(x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_3);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unbox(x_22);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
return x_38;
}
block_79:
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_inc(x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_unbox(x_22);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_52);
lean_inc(x_45);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
x_57 = lean_mk_string_unchecked("ccLinkSharedFlags", 17, 17);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_9);
x_61 = lean_ctor_get(x_1, 18);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_array_get_size(x_61);
x_63 = lean_nat_dec_eq(x_62, x_14);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_64 = lean_mk_string_unchecked("#[", 2, 2);
x_65 = lean_array_to_list(x_61);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_45);
lean_ctor_set(x_66, 1, x_47);
x_67 = l_Std_Format_joinSep(lean_box(0), x_2, x_65, x_66);
x_68 = lean_mk_string_unchecked("]", 1, 1);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_to_int(x_69);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_64);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Std_Format_fill(x_75);
x_23 = x_60;
x_24 = x_49;
x_25 = x_76;
goto block_40;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_61);
lean_dec(x_45);
lean_dec(x_2);
x_77 = lean_mk_string_unchecked("#[]", 3, 3);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_23 = x_60;
x_24 = x_49;
x_25 = x_78;
goto block_40;
}
}
block_112:
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_unbox(x_22);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_84);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_83);
lean_inc(x_45);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_45);
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_47);
x_88 = lean_mk_string_unchecked("ccLinkStaticFlags", 17, 17);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
lean_inc(x_9);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_9);
x_92 = lean_unsigned_to_nat(21u);
x_93 = lean_nat_to_int(x_92);
x_94 = lean_ctor_get(x_1, 17);
lean_inc(x_94);
x_95 = lean_array_get_size(x_94);
x_96 = lean_nat_dec_eq(x_95, x_14);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_mk_string_unchecked("#[", 2, 2);
x_98 = lean_array_to_list(x_94);
lean_inc(x_45);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_45);
lean_ctor_set(x_99, 1, x_47);
lean_inc(x_2);
x_100 = l_Std_Format_joinSep(lean_box(0), x_2, x_98, x_99);
x_101 = lean_mk_string_unchecked("]", 1, 1);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_to_int(x_102);
x_104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_104, 0, x_97);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Std_Format_fill(x_108);
x_48 = x_91;
x_49 = x_93;
x_50 = x_109;
goto block_79;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_94);
x_110 = lean_mk_string_unchecked("#[]", 3, 3);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_48 = x_91;
x_49 = x_93;
x_50 = x_111;
goto block_79;
}
}
block_144:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_116 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_unbox(x_22);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_118);
x_119 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_119, 0, x_113);
lean_ctor_set(x_119, 1, x_117);
lean_inc(x_45);
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_45);
x_121 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_47);
x_122 = lean_mk_string_unchecked("ccFlags", 7, 7);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
lean_inc(x_9);
x_125 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_9);
x_126 = lean_ctor_get(x_1, 16);
lean_inc(x_126);
x_127 = lean_array_get_size(x_126);
x_128 = lean_nat_dec_eq(x_127, x_14);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_129 = lean_mk_string_unchecked("#[", 2, 2);
x_130 = lean_array_to_list(x_126);
lean_inc(x_45);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_45);
lean_ctor_set(x_131, 1, x_47);
lean_inc(x_2);
x_132 = l_Std_Format_joinSep(lean_box(0), x_2, x_130, x_131);
x_133 = lean_mk_string_unchecked("]", 1, 1);
x_134 = lean_unsigned_to_nat(2u);
x_135 = lean_nat_to_int(x_134);
x_136 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_136, 0, x_129);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_132);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_133);
x_139 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Std_Format_fill(x_140);
x_80 = x_125;
x_81 = x_141;
goto block_112;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_126);
x_142 = lean_mk_string_unchecked("#[]", 3, 3);
x_143 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_80 = x_125;
x_81 = x_143;
goto block_112;
}
}
block_176:
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_inc(x_146);
x_148 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_unbox(x_22);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_150);
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_149);
lean_inc(x_45);
x_152 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_45);
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_47);
x_154 = lean_mk_string_unchecked("linkSharedFlags", 15, 15);
x_155 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
lean_inc(x_9);
x_157 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_9);
x_158 = lean_ctor_get(x_1, 15);
lean_inc(x_158);
x_159 = lean_array_get_size(x_158);
x_160 = lean_nat_dec_eq(x_159, x_14);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_161 = lean_mk_string_unchecked("#[", 2, 2);
x_162 = lean_array_to_list(x_158);
lean_inc(x_45);
x_163 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_163, 0, x_45);
lean_ctor_set(x_163, 1, x_47);
lean_inc(x_2);
x_164 = l_Std_Format_joinSep(lean_box(0), x_2, x_162, x_163);
x_165 = lean_mk_string_unchecked("]", 1, 1);
x_166 = lean_unsigned_to_nat(2u);
x_167 = lean_nat_to_int(x_166);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_161);
x_169 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
x_170 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_171 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Std_Format_fill(x_172);
x_113 = x_157;
x_114 = x_146;
x_115 = x_173;
goto block_144;
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_158);
x_174 = lean_mk_string_unchecked("#[]", 3, 3);
x_175 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_113 = x_157;
x_114 = x_146;
x_115 = x_175;
goto block_144;
}
}
block_229:
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_199 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_unbox(x_22);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_201);
x_202 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_200);
lean_inc(x_45);
x_203 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_45);
x_204 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_47);
x_205 = lean_mk_string_unchecked("linkStaticFlags", 15, 15);
x_206 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_206);
lean_inc(x_9);
x_208 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_9);
x_209 = lean_unsigned_to_nat(19u);
x_210 = lean_nat_to_int(x_209);
x_211 = lean_ctor_get(x_1, 14);
lean_inc(x_211);
x_212 = lean_array_get_size(x_211);
x_213 = lean_nat_dec_eq(x_212, x_14);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_214 = lean_mk_string_unchecked("#[", 2, 2);
x_215 = lean_array_to_list(x_211);
lean_inc(x_45);
x_216 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_216, 0, x_45);
lean_ctor_set(x_216, 1, x_47);
lean_inc(x_2);
x_217 = l_Std_Format_joinSep(lean_box(0), x_2, x_215, x_216);
x_218 = lean_mk_string_unchecked("]", 1, 1);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_nat_to_int(x_219);
x_221 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_221, 0, x_214);
x_222 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_217);
x_223 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_223, 0, x_218);
x_224 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Std_Format_fill(x_225);
x_145 = x_208;
x_146 = x_210;
x_147 = x_226;
goto block_176;
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_211);
x_227 = lean_mk_string_unchecked("#[]", 3, 3);
x_228 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_145 = x_208;
x_146 = x_210;
x_147 = x_228;
goto block_176;
}
}
block_440:
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_412 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_413, 0, x_412);
x_414 = lean_unbox(x_22);
lean_ctor_set_uint8(x_413, sizeof(void*)*1, x_414);
x_415 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_415, 0, x_408);
lean_ctor_set(x_415, 1, x_413);
lean_inc(x_45);
x_416 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_45);
x_417 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_47);
x_418 = lean_mk_string_unchecked("cFlags", 6, 6);
x_419 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_419, 0, x_418);
x_420 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_419);
lean_inc(x_9);
x_421 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_9);
x_422 = lean_ctor_get(x_1, 13);
lean_inc(x_422);
x_423 = lean_array_get_size(x_422);
x_424 = lean_nat_dec_eq(x_423, x_14);
lean_dec(x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_425 = lean_mk_string_unchecked("#[", 2, 2);
x_426 = lean_array_to_list(x_422);
lean_inc(x_45);
x_427 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_427, 0, x_45);
lean_ctor_set(x_427, 1, x_47);
lean_inc(x_2);
x_428 = l_Std_Format_joinSep(lean_box(0), x_2, x_426, x_427);
x_429 = lean_mk_string_unchecked("]", 1, 1);
x_430 = lean_unsigned_to_nat(2u);
x_431 = lean_nat_to_int(x_430);
x_432 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_432, 0, x_425);
x_433 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_428);
x_434 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_434, 0, x_429);
x_435 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
x_436 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_436, 0, x_431);
lean_ctor_set(x_436, 1, x_435);
x_437 = l_Std_Format_fill(x_436);
x_197 = x_421;
x_198 = x_437;
goto block_229;
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_422);
x_438 = lean_mk_string_unchecked("#[]", 3, 3);
x_439 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_439, 0, x_438);
x_197 = x_421;
x_198 = x_439;
goto block_229;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall____x40_Lake_Config_InstallPath___hyg_537_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg____x40_Lake_Config_InstallPath___hyg_537_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg___lam__0____x40_Lake_Config_InstallPath___hyg_537____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall___redArg___lam__0____x40_Lake_Config_InstallPath___hyg_537_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall____x40_Lake_Config_InstallPath___hyg_537____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall____x40_Lake_Config_InstallPath___hyg_537_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprLeanInstall() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_InstallPath_0__Lake_reprLeanInstall____x40_Lake_Config_InstallPath___hyg_537____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_1, 5);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 6);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_sharedLibPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LeanInstall_sharedLibPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*19);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 12);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LeanInstall_leanCc_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 17);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 18);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_ccLinkFlags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_LeanInstall_ccLinkFlags(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_lakeExe() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
x_2 = l_System_FilePath_exeExtension;
x_3 = l_System_FilePath_addExtension(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedLakeInstall() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("", 0, 0);
lean_inc_n(x_1, 5);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall___redArg____x40_Lake_Config_InstallPath___hyg_1116_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("home", 4, 4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_String_quote(x_12);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_13);
lean_inc(x_11);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_mk_string_unchecked(",", 1, 1);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("srcDir", 6, 6);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_8);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_unsigned_to_nat(10u);
x_35 = lean_nat_to_int(x_34);
x_36 = lean_ctor_get(x_1, 1);
x_37 = l_String_quote(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_15);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Repr_addAppParen(x_39, x_13);
lean_inc(x_35);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_unbox(x_21);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_42);
lean_inc(x_26);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_26);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_28);
x_47 = lean_mk_string_unchecked("binDir", 6, 6);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_8);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_8);
x_51 = lean_ctor_get(x_1, 2);
x_52 = l_String_quote(x_51);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_15);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_15);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Repr_addAppParen(x_54, x_13);
lean_inc(x_35);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_35);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_unbox(x_21);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_57);
lean_inc(x_26);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_26);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_28);
x_62 = lean_mk_string_unchecked("libDir", 6, 6);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_8);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
x_66 = lean_ctor_get(x_1, 3);
x_67 = l_String_quote(x_66);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_inc(x_15);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_15);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Repr_addAppParen(x_69, x_13);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_35);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_unbox(x_21);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_73);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_72);
lean_inc(x_26);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_28);
x_77 = lean_mk_string_unchecked("sharedLib", 9, 9);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_8);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_8);
x_81 = lean_unsigned_to_nat(13u);
x_82 = lean_nat_to_int(x_81);
x_83 = lean_ctor_get(x_1, 4);
x_84 = l_String_quote(x_83);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_inc(x_15);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_15);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Repr_addAppParen(x_86, x_13);
x_88 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_unbox(x_21);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_26);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_28);
x_94 = lean_mk_string_unchecked("lake", 4, 4);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_8);
x_98 = lean_ctor_get(x_1, 5);
x_99 = l_String_quote(x_98);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_15);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Repr_addAppParen(x_101, x_13);
x_103 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_103, 0, x_11);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_unbox(x_21);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_105);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_mk_string_unchecked(" }", 2, 2);
x_108 = lean_unsigned_to_nat(2u);
x_109 = lean_nat_to_int(x_108);
x_110 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_110, 0, x_2);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_unbox(x_21);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_116);
return x_115;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall____x40_Lake_Config_InstallPath___hyg_1116_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall___redArg____x40_Lake_Config_InstallPath___hyg_1116_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall___redArg____x40_Lake_Config_InstallPath___hyg_1116____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall___redArg____x40_Lake_Config_InstallPath___hyg_1116_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall____x40_Lake_Config_InstallPath___hyg_1116____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall____x40_Lake_Config_InstallPath___hyg_1116_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprLakeInstall() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_InstallPath_0__Lake_reprLakeInstall____x40_Lake_Config_InstallPath___hyg_1116____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeInstall_ofLean(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_mk_string_unchecked("lake", 4, 4);
x_5 = l_System_FilePath_join(x_3, x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("libLake_shared.", 15, 15);
x_14 = l_Lake_sharedLibExt;
x_15 = l_System_Platform_isWindows;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_string_append(x_13, x_14);
lean_inc(x_7);
x_17 = l_System_FilePath_join(x_7, x_16);
lean_dec(x_16);
x_8 = x_17;
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_string_append(x_13, x_14);
lean_inc(x_6);
x_19 = l_System_FilePath_join(x_6, x_18);
lean_dec(x_18);
x_8 = x_19;
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lake_lakeExe;
lean_inc(x_6);
x_10 = l_System_FilePath_join(x_6, x_9);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set(x_11, 5, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findElanInstall_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("ELAN_HOME", 9, 9);
x_3 = lean_io_getenv(x_2, x_1);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_13 = x_4;
} else {
 lean_dec_ref(x_4);
 x_13 = lean_box(0);
}
x_14 = lean_mk_string_unchecked("ELAN", 4, 4);
x_15 = lean_io_getenv(x_14, x_11);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_37; 
x_37 = lean_mk_string_unchecked("elan", 4, 4);
x_19 = x_37;
goto block_36;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
lean_dec(x_16);
x_19 = x_38;
goto block_36;
}
block_36:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_byte_size(x_19);
x_22 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_19, x_21, x_20);
x_23 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_19, x_22, x_21);
x_24 = lean_string_utf8_extract(x_19, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_string_utf8_byte_size(x_24);
lean_dec(x_24);
x_26 = l_instDecidableEqPos(x_25, x_20);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_mk_string_unchecked("bin", 3, 3);
lean_inc(x_12);
x_28 = l_System_FilePath_join(x_12, x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("toolchains", 10, 10);
lean_inc(x_12);
x_30 = l_System_FilePath_join(x_12, x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_30);
if (lean_is_scalar(x_13)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_13;
}
lean_ctor_set(x_32, 0, x_31);
if (lean_is_scalar(x_18)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_18;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
x_34 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_18;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_17);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_findLeanSysroot_x3f_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_4, x_3);
if (x_9 == 0)
{
return x_4;
}
else
{
uint32_t x_10; uint8_t x_11; uint8_t x_16; lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_10 = lean_string_utf8_get(x_2, x_4);
x_21 = lean_unsigned_to_nat(32u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_10, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(9u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_10, x_25);
x_16 = x_26;
goto block_20;
}
else
{
x_16 = x_1;
goto block_20;
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(10u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_10, x_13);
x_5 = x_14;
goto block_8;
}
else
{
x_5 = x_1;
goto block_8;
}
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(13u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_10, x_18);
x_11 = x_19;
goto block_15;
}
else
{
x_11 = x_1;
goto block_15;
}
}
}
block_8:
{
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_findLeanSysroot_x3f_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; uint32_t x_10; uint8_t x_11; uint8_t x_16; lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_6 = lean_string_utf8_prev(x_2, x_4);
x_10 = lean_string_utf8_get(x_2, x_6);
x_21 = lean_unsigned_to_nat(32u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_10, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(9u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_10, x_25);
x_16 = x_26;
goto block_20;
}
else
{
x_16 = x_1;
goto block_20;
}
block_9:
{
if (x_7 == 0)
{
lean_dec(x_6);
return x_4;
}
else
{
lean_dec(x_4);
x_4 = x_6;
goto _start;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(10u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_10, x_13);
x_7 = x_14;
goto block_9;
}
else
{
x_7 = x_1;
goto block_9;
}
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(13u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_10, x_18);
x_11 = x_19;
goto block_15;
}
else
{
x_11 = x_1;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanSysroot_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 0, 3);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 0, x_5);
x_6 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 1, x_6);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 2, x_7);
x_8 = lean_mk_string_unchecked("--print-prefix", 14, 14);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_8);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_box(1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_14);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_18);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_19);
x_20 = l_IO_Process_output(x_17, x_2);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint32_t x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get_uint32(x_22, sizeof(void*)*2);
x_24 = lean_uint32_of_nat(x_13);
x_25 = lean_uint32_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_12);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = l_Substring_takeWhileAux___at___Lake_findLeanSysroot_x3f_spec__0(x_25, x_26, x_27, x_13);
x_29 = l_Substring_takeRightWhileAux___at___Lake_findLeanSysroot_x3f_spec__1(x_25, x_26, x_28, x_27);
x_30 = lean_string_utf8_extract(x_26, x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_20, 0, x_31);
return x_20;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint32_t x_34; uint32_t x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_ctor_get_uint32(x_32, sizeof(void*)*2);
x_35 = lean_uint32_of_nat(x_13);
x_36 = lean_uint32_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_string_utf8_byte_size(x_38);
x_40 = l_Substring_takeWhileAux___at___Lake_findLeanSysroot_x3f_spec__0(x_36, x_38, x_39, x_13);
x_41 = l_Substring_takeRightWhileAux___at___Lake_findLeanSysroot_x3f_spec__1(x_36, x_38, x_40, x_39);
x_42 = lean_string_utf8_extract(x_38, x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_33);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_20, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_12);
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_findLeanSysroot_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Substring_takeWhileAux___at___Lake_findLeanSysroot_x3f_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_findLeanSysroot_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Substring_takeRightWhileAux___at___Lake_findLeanSysroot_x3f_spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_getGithash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 0, 3);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 0, x_5);
x_6 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 1, x_6);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 2, x_7);
x_8 = l_Lake_leanExe(x_1);
x_9 = lean_mk_string_unchecked("--githash", 9, 9);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_9);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_box(1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_15);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_19);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_20);
x_21 = l_IO_Process_output(x_18, x_2);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_string_utf8_byte_size(x_24);
x_26 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_24, x_25, x_14);
x_27 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_24, x_26, x_25);
x_28 = lean_string_utf8_extract(x_24, x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_utf8_byte_size(x_31);
x_33 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_31, x_32, x_14);
x_34 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_31, x_33, x_32);
x_35 = lean_string_utf8_extract(x_31, x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_21, 0);
lean_dec(x_38);
x_39 = lean_mk_string_unchecked("", 0, 0);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_findAr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("LEAN_AR", 7, 7);
x_4 = lean_io_getenv(x_3, x_2);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lake_leanArExe(x_1);
x_8 = l_System_FilePath_pathExists(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("AR", 2, 2);
x_13 = lean_io_getenv(x_12, x_11);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_mk_string_unchecked("ar", 2, 2);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_mk_string_unchecked("ar", 2, 2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_8, 0);
lean_dec(x_28);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withInternalCc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_4 = l_Lean_Compiler_FFI_getInternalLinkerFlags(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 7);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 8);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 9);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 10);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 11);
lean_inc(x_16);
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_2, 13);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 14);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 15);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_Compiler_FFI_getInternalCFlags(x_1);
lean_inc(x_18);
x_22 = l_Array_append(lean_box(0), x_18, x_21);
lean_dec(x_21);
lean_inc(x_4);
x_23 = l_Array_append(lean_box(0), x_4, x_19);
x_24 = l_Array_append(lean_box(0), x_4, x_20);
x_25 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_8);
lean_ctor_set(x_25, 4, x_9);
lean_ctor_set(x_25, 5, x_10);
lean_ctor_set(x_25, 6, x_11);
lean_ctor_set(x_25, 7, x_12);
lean_ctor_set(x_25, 8, x_13);
lean_ctor_set(x_25, 9, x_14);
lean_ctor_set(x_25, 10, x_15);
lean_ctor_set(x_25, 11, x_16);
lean_ctor_set(x_25, 12, x_3);
lean_ctor_set(x_25, 13, x_18);
lean_ctor_set(x_25, 14, x_19);
lean_ctor_set(x_25, 15, x_20);
lean_ctor_set(x_25, 16, x_22);
lean_ctor_set(x_25, 17, x_23);
lean_ctor_set(x_25, 18, x_24);
x_26 = lean_unbox(x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*19, x_26);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withInternalCc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_LeanInstall_get_withInternalCc(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withCustomCc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = lean_ctor_get(x_1, 9);
x_13 = lean_ctor_get(x_1, 10);
x_14 = lean_ctor_get(x_1, 11);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*19);
x_16 = lean_ctor_get(x_1, 13);
x_17 = lean_ctor_get(x_1, 14);
x_18 = lean_ctor_get(x_1, 15);
x_19 = lean_ctor_get(x_1, 16);
x_20 = lean_ctor_get(x_1, 17);
x_21 = lean_ctor_get(x_1, 18);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_5);
lean_ctor_set(x_22, 3, x_6);
lean_ctor_set(x_22, 4, x_7);
lean_ctor_set(x_22, 5, x_8);
lean_ctor_set(x_22, 6, x_9);
lean_ctor_set(x_22, 7, x_10);
lean_ctor_set(x_22, 8, x_11);
lean_ctor_set(x_22, 9, x_12);
lean_ctor_set(x_22, 10, x_13);
lean_ctor_set(x_22, 11, x_14);
lean_ctor_set(x_22, 12, x_2);
lean_ctor_set(x_22, 13, x_16);
lean_ctor_set(x_22, 14, x_17);
lean_ctor_set(x_22, 15, x_18);
lean_ctor_set(x_22, 16, x_19);
lean_ctor_set(x_22, 17, x_20);
lean_ctor_set(x_22, 18, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*19, x_15);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_withCustomCc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_LeanInstall_get_withCustomCc(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get_setCc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_mk_string_unchecked("LEAN_CC", 7, 7);
x_29 = lean_io_getenv(x_28, x_3);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
x_32 = l_Lake_leanCcExe(x_1);
x_33 = l_System_FilePath_pathExists(x_32, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_1);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_mk_string_unchecked("CC", 2, 2);
x_38 = lean_io_getenv(x_37, x_36);
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_mk_string_unchecked("cc", 2, 2);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 7);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 8);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 9);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 10);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 11);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*19);
x_56 = lean_ctor_get(x_2, 13);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 14);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 15);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 16);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 17);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 18);
lean_inc(x_61);
lean_dec(x_2);
x_62 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set(x_62, 2, x_45);
lean_ctor_set(x_62, 3, x_46);
lean_ctor_set(x_62, 4, x_47);
lean_ctor_set(x_62, 5, x_48);
lean_ctor_set(x_62, 6, x_49);
lean_ctor_set(x_62, 7, x_50);
lean_ctor_set(x_62, 8, x_51);
lean_ctor_set(x_62, 9, x_52);
lean_ctor_set(x_62, 10, x_53);
lean_ctor_set(x_62, 11, x_54);
lean_ctor_set(x_62, 12, x_42);
lean_ctor_set(x_62, 13, x_56);
lean_ctor_set(x_62, 14, x_57);
lean_ctor_set(x_62, 15, x_58);
lean_ctor_set(x_62, 16, x_59);
lean_ctor_set(x_62, 17, x_60);
lean_ctor_set(x_62, 18, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*19, x_55);
lean_ctor_set(x_38, 0, x_62);
return x_38;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_63 = lean_ctor_get(x_38, 1);
lean_inc(x_63);
lean_dec(x_38);
x_64 = lean_mk_string_unchecked("cc", 2, 2);
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 7);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 8);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 9);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 10);
lean_inc(x_75);
x_76 = lean_ctor_get(x_2, 11);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*19);
x_78 = lean_ctor_get(x_2, 13);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 14);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 15);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 16);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 17);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 18);
lean_inc(x_83);
lean_dec(x_2);
x_84 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_84, 0, x_65);
lean_ctor_set(x_84, 1, x_66);
lean_ctor_set(x_84, 2, x_67);
lean_ctor_set(x_84, 3, x_68);
lean_ctor_set(x_84, 4, x_69);
lean_ctor_set(x_84, 5, x_70);
lean_ctor_set(x_84, 6, x_71);
lean_ctor_set(x_84, 7, x_72);
lean_ctor_set(x_84, 8, x_73);
lean_ctor_set(x_84, 9, x_74);
lean_ctor_set(x_84, 10, x_75);
lean_ctor_set(x_84, 11, x_76);
lean_ctor_set(x_84, 12, x_64);
lean_ctor_set(x_84, 13, x_78);
lean_ctor_set(x_84, 14, x_79);
lean_ctor_set(x_84, 15, x_80);
lean_ctor_set(x_84, 16, x_81);
lean_ctor_set(x_84, 17, x_82);
lean_ctor_set(x_84, 18, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*19, x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_63);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_38, 1);
lean_inc(x_86);
lean_dec(x_38);
x_87 = lean_ctor_get(x_39, 0);
lean_inc(x_87);
lean_dec(x_39);
x_4 = x_87;
x_5 = x_86;
goto block_27;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_33);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_33, 0);
lean_dec(x_89);
x_90 = l_Lake_LeanInstall_get_withInternalCc(x_1, x_2, x_32);
lean_dec(x_1);
lean_ctor_set(x_33, 0, x_90);
return x_33;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_33, 1);
lean_inc(x_91);
lean_dec(x_33);
x_92 = l_Lake_LeanInstall_get_withInternalCc(x_1, x_2, x_32);
lean_dec(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_94 = lean_ctor_get(x_29, 1);
lean_inc(x_94);
lean_dec(x_29);
x_95 = lean_ctor_get(x_30, 0);
lean_inc(x_95);
lean_dec(x_30);
x_4 = x_95;
x_5 = x_94;
goto block_27;
}
block_27:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 7);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 8);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 9);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 10);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 11);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*19);
x_19 = lean_ctor_get(x_2, 13);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 14);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 15);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 16);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 17);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 18);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_8);
lean_ctor_set(x_25, 3, x_9);
lean_ctor_set(x_25, 4, x_10);
lean_ctor_set(x_25, 5, x_11);
lean_ctor_set(x_25, 6, x_12);
lean_ctor_set(x_25, 7, x_13);
lean_ctor_set(x_25, 8, x_14);
lean_ctor_set(x_25, 9, x_15);
lean_ctor_set(x_25, 10, x_16);
lean_ctor_set(x_25, 11, x_17);
lean_ctor_set(x_25, 12, x_4);
lean_ctor_set(x_25, 13, x_19);
lean_ctor_set(x_25, 14, x_20);
lean_ctor_set(x_25, 15, x_21);
lean_ctor_set(x_25, 16, x_22);
lean_ctor_set(x_25, 17, x_23);
lean_ctor_set(x_25, 18, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*19, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (x_2 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_1);
x_41 = l_Lake_LeanInstall_get_getGithash(x_1, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_4 = x_42;
x_5 = x_43;
goto block_40;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_githash;
x_4 = x_44;
x_5 = x_3;
goto block_40;
}
block_40:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_inc(x_1);
x_6 = l_Lake_LeanInstall_get_findAr(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_mk_string_unchecked("src", 3, 3);
lean_inc(x_1);
x_10 = l_System_FilePath_join(x_1, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("lean", 4, 4);
x_12 = l_System_FilePath_join(x_10, x_11);
x_13 = lean_mk_string_unchecked("lib", 3, 3);
lean_inc(x_1);
x_14 = l_System_FilePath_join(x_1, x_13);
lean_dec(x_13);
lean_inc(x_14);
x_15 = l_System_FilePath_join(x_14, x_11);
lean_dec(x_11);
x_16 = lean_mk_string_unchecked("include", 7, 7);
lean_inc(x_1);
x_17 = l_System_FilePath_join(x_1, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("bin", 3, 3);
lean_inc(x_1);
x_19 = l_System_FilePath_join(x_1, x_18);
lean_dec(x_18);
lean_inc(x_1);
x_20 = l_Lake_leanExe(x_1);
lean_inc(x_1);
x_21 = l_Lake_leancExe(x_1);
lean_inc(x_1);
x_22 = l_Lake_leanSharedLibDir(x_1);
x_23 = l_Lake_leanSharedLib;
lean_inc(x_22);
x_24 = l_System_FilePath_join(x_22, x_23);
x_25 = l_Lake_initSharedLib;
x_26 = l_System_FilePath_join(x_22, x_25);
x_27 = lean_mk_string_unchecked("cc", 2, 2);
x_28 = lean_box(1);
x_29 = l_Lean_Compiler_FFI_getCFlags_x27;
x_30 = lean_mk_string_unchecked("-Wno-unused-command-line-argument", 33, 33);
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_unbox(x_28);
x_33 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_32);
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
x_36 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_35);
lean_inc(x_36);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_1);
x_37 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 2, x_12);
lean_ctor_set(x_37, 3, x_15);
lean_ctor_set(x_37, 4, x_17);
lean_ctor_set(x_37, 5, x_14);
lean_ctor_set(x_37, 6, x_19);
lean_ctor_set(x_37, 7, x_20);
lean_ctor_set(x_37, 8, x_21);
lean_ctor_set(x_37, 9, x_24);
lean_ctor_set(x_37, 10, x_26);
lean_ctor_set(x_37, 11, x_7);
lean_ctor_set(x_37, 12, x_27);
lean_ctor_set(x_37, 13, x_31);
lean_ctor_set(x_37, 14, x_33);
lean_ctor_set(x_37, 15, x_36);
lean_ctor_set(x_37, 16, x_31);
lean_ctor_set(x_37, 17, x_33);
lean_ctor_set(x_37, 18, x_36);
x_38 = lean_unbox(x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*19, x_38);
x_39 = l_Lake_LeanInstall_get_setCc(x_1, x_37, x_8);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanInstall_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_LeanInstall_get(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanCmdInstall_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_findLeanSysroot_x3f(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lake_LeanInstall_get(x_13, x_15, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_4, 0, x_18);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_4, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lake_LeanInstall_get(x_22, x_24, x_11);
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
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
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
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeLeanJointHome_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_6; 
x_6 = lean_io_app_path(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_System_FilePath_parent(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
x_2 = x_8;
goto block_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("lean", 4, 4);
lean_inc(x_10);
x_12 = l_System_FilePath_join(x_10, x_11);
lean_dec(x_11);
x_13 = l_System_FilePath_exeExtension;
x_14 = l_System_FilePath_addExtension(x_12, x_13);
x_15 = l_System_FilePath_pathExists(x_14, x_8);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_10);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_2 = x_18;
goto block_5;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = l_System_FilePath_parent(x_10);
lean_dec(x_10);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_System_FilePath_parent(x_10);
lean_dec(x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_2 = x_25;
goto block_5;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_System_FilePath_parent(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_System_FilePath_parent(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_System_FilePath_parent(x_7);
lean_dec(x_7);
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_lakeBuildHome_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_lakeBuildHome_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_lakeBuildHome_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = l_Lake_defaultBuildDir;
lean_inc(x_7);
x_9 = l_System_FilePath_join(x_7, x_8);
x_10 = l_Lake_defaultLeanLibDir;
lean_inc(x_9);
x_11 = l_System_FilePath_join(x_9, x_10);
x_12 = lean_mk_string_unchecked("Lake", 4, 4);
x_13 = lean_mk_string_unchecked("Lake.olean", 10, 10);
lean_inc(x_11);
x_14 = l_System_FilePath_join(x_11, x_13);
lean_dec(x_13);
x_15 = l_System_FilePath_pathExists(x_14, x_2);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = l_Lake_defaultBinDir;
x_27 = l_Lake_nameToSharedLib(x_12);
x_28 = l_System_FilePath_join(x_9, x_26);
lean_inc(x_11);
x_29 = l_System_FilePath_join(x_11, x_27);
lean_dec(x_27);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_11);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_1);
lean_ctor_set(x_3, 0, x_30);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = l_Lake_defaultBinDir;
x_33 = l_Lake_nameToSharedLib(x_12);
x_34 = l_System_FilePath_join(x_9, x_32);
lean_inc(x_11);
x_35 = l_System_FilePath_join(x_11, x_33);
lean_dec(x_33);
lean_inc(x_7);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_7);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_11);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_1);
lean_ctor_set(x_3, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = l_Lake_defaultBuildDir;
lean_inc(x_38);
x_40 = l_System_FilePath_join(x_38, x_39);
x_41 = l_Lake_defaultLeanLibDir;
lean_inc(x_40);
x_42 = l_System_FilePath_join(x_40, x_41);
x_43 = lean_mk_string_unchecked("Lake", 4, 4);
x_44 = lean_mk_string_unchecked("Lake.olean", 10, 10);
lean_inc(x_42);
x_45 = l_System_FilePath_join(x_42, x_44);
lean_dec(x_44);
x_46 = l_System_FilePath_pathExists(x_45, x_2);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_1);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_54 = x_46;
} else {
 lean_dec_ref(x_46);
 x_54 = lean_box(0);
}
x_55 = l_Lake_defaultBinDir;
x_56 = l_Lake_nameToSharedLib(x_43);
x_57 = l_System_FilePath_join(x_40, x_55);
lean_inc(x_42);
x_58 = l_System_FilePath_join(x_42, x_56);
lean_dec(x_56);
lean_inc(x_38);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_38);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_42);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_1);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_53);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanInstall_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
x_3 = lean_io_getenv(x_2, x_1);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_mk_string_unchecked("LEAN", 4, 4);
x_7 = lean_io_getenv(x_6, x_5);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_41; 
lean_free_object(x_7);
x_41 = lean_mk_string_unchecked("lean", 4, 4);
x_11 = x_41;
goto block_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_string_utf8_byte_size(x_42);
x_45 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_42, x_44, x_43);
x_46 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_42, x_45, x_44);
x_47 = lean_string_utf8_extract(x_42, x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
x_48 = lean_string_utf8_byte_size(x_47);
lean_dec(x_47);
x_49 = l_instDecidableEqPos(x_48, x_43);
lean_dec(x_48);
if (x_49 == 0)
{
lean_free_object(x_7);
x_11 = x_42;
goto block_40;
}
else
{
lean_object* x_50; 
lean_dec(x_42);
x_50 = lean_box(0);
lean_ctor_set(x_7, 0, x_50);
return x_7;
}
}
block_40:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lake_findLeanSysroot_x3f(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lake_LeanInstall_get(x_22, x_24, x_20);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_13, 0, x_27);
lean_ctor_set(x_25, 0, x_13);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_13, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
x_34 = l_Lake_LeanInstall_get(x_31, x_33, x_20);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 0);
x_52 = lean_ctor_get(x_7, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_72; 
x_72 = lean_mk_string_unchecked("lean", 4, 4);
x_53 = x_72;
goto block_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_51, 0);
lean_inc(x_73);
lean_dec(x_51);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_string_utf8_byte_size(x_73);
x_76 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_73, x_75, x_74);
x_77 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_73, x_76, x_75);
x_78 = lean_string_utf8_extract(x_73, x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
x_79 = lean_string_utf8_byte_size(x_78);
lean_dec(x_78);
x_80 = l_instDecidableEqPos(x_79, x_74);
lean_dec(x_79);
if (x_80 == 0)
{
x_53 = x_73;
goto block_71;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_73);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_52);
return x_82;
}
}
block_71:
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lake_findLeanSysroot_x3f(x_53, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
x_64 = lean_unbox(x_63);
x_65 = l_Lake_LeanInstall_get(x_61, x_64, x_60);
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
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_62;
}
lean_ctor_set(x_69, 0, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_3, 1);
lean_inc(x_83);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_4);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_4, 0);
x_86 = lean_box(0);
x_87 = lean_unbox(x_86);
x_88 = l_Lake_LeanInstall_get(x_85, x_87, x_83);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_88, 0);
lean_ctor_set(x_4, 0, x_90);
lean_ctor_set(x_88, 0, x_4);
return x_88;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_88, 0);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_88);
lean_ctor_set(x_4, 0, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_4);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = lean_ctor_get(x_4, 0);
lean_inc(x_94);
lean_dec(x_4);
x_95 = lean_box(0);
x_96 = lean_unbox(x_95);
x_97 = l_Lake_LeanInstall_get(x_94, x_96, x_83);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_98);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findLakeInstall_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_60; 
x_60 = lean_io_app_path(x_1);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lake_getLakeInstall_x3f(x_61, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_2 = x_65;
goto block_59;
}
else
{
lean_dec(x_64);
return x_63;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_2 = x_66;
goto block_59;
}
block_59:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("LAKE_HOME", 9, 9);
x_4 = lean_io_getenv(x_3, x_2);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = l_Lake_defaultBuildDir;
lean_inc(x_15);
x_17 = l_System_FilePath_join(x_15, x_16);
x_18 = l_Lake_defaultBinDir;
lean_inc(x_17);
x_19 = l_System_FilePath_join(x_17, x_18);
x_20 = l_Lake_defaultLeanLibDir;
x_21 = l_System_FilePath_join(x_17, x_20);
x_22 = lean_mk_string_unchecked("Lake", 4, 4);
x_23 = l_Lake_nameToSharedLib(x_22);
lean_inc(x_21);
x_24 = l_System_FilePath_join(x_21, x_23);
lean_dec(x_23);
x_25 = l_Lake_lakeExe;
lean_inc(x_19);
x_26 = l_System_FilePath_join(x_19, x_25);
lean_inc(x_15);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_19);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_5, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = l_Lake_defaultBuildDir;
lean_inc(x_28);
x_30 = l_System_FilePath_join(x_28, x_29);
x_31 = l_Lake_defaultBinDir;
lean_inc(x_30);
x_32 = l_System_FilePath_join(x_30, x_31);
x_33 = l_Lake_defaultLeanLibDir;
x_34 = l_System_FilePath_join(x_30, x_33);
x_35 = lean_mk_string_unchecked("Lake", 4, 4);
x_36 = l_Lake_nameToSharedLib(x_35);
lean_inc(x_34);
x_37 = l_System_FilePath_join(x_34, x_36);
lean_dec(x_36);
x_38 = l_Lake_lakeExe;
lean_inc(x_32);
x_39 = l_System_FilePath_join(x_32, x_38);
lean_inc(x_28);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_4, 0, x_41);
return x_4;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_dec(x_4);
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_44 = x_5;
} else {
 lean_dec_ref(x_5);
 x_44 = lean_box(0);
}
x_45 = l_Lake_defaultBuildDir;
lean_inc(x_43);
x_46 = l_System_FilePath_join(x_43, x_45);
x_47 = l_Lake_defaultBinDir;
lean_inc(x_46);
x_48 = l_System_FilePath_join(x_46, x_47);
x_49 = l_Lake_defaultLeanLibDir;
x_50 = l_System_FilePath_join(x_46, x_49);
x_51 = lean_mk_string_unchecked("Lake", 4, 4);
x_52 = l_Lake_nameToSharedLib(x_51);
lean_inc(x_50);
x_53 = l_System_FilePath_join(x_50, x_52);
lean_dec(x_52);
x_54 = l_Lake_lakeExe;
lean_inc(x_48);
x_55 = l_System_FilePath_join(x_48, x_54);
lean_inc(x_43);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_48);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_53);
lean_ctor_set(x_56, 5, x_55);
if (lean_is_scalar(x_44)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_44;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_42);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_findInstall_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lake_findElanInstall_x3f(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lake_findLakeLeanJointHome_x3f(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_free_object(x_2);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = l_Lake_findLeanInstall_x3f(x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l_Lake_findLakeInstall_x3f(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_11, 1, x_16);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_14, 0, x_6);
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
lean_ctor_set(x_11, 1, x_17);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = l_Lake_findLakeInstall_x3f(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
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
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_4);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_dec(x_6);
x_29 = l_Lake_findLeanInstall_x3f(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = l_Lake_findLakeInstall_x3f(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_37);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_41 = x_6;
} else {
 lean_dec_ref(x_6);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_43 = x_7;
} else {
 lean_dec_ref(x_7);
 x_43 = lean_box(0);
}
x_44 = lean_mk_string_unchecked("LAKE_OVERRIDE_LEAN", 18, 18);
x_45 = lean_io_getenv(x_44, x_40);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_obj_tag(x_46) == 0)
{
lean_free_object(x_2);
goto block_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_46, 0);
lean_inc(x_68);
lean_dec(x_46);
x_69 = l_Lake_envToBool_x3f(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_free_object(x_2);
goto block_67;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_unbox(x_71);
if (x_72 == 0)
{
lean_free_object(x_69);
lean_dec(x_71);
lean_free_object(x_2);
goto block_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_41);
x_73 = lean_mk_string_unchecked("src", 3, 3);
lean_inc(x_42);
x_74 = l_System_FilePath_join(x_42, x_73);
lean_dec(x_73);
x_75 = lean_mk_string_unchecked("lean", 4, 4);
x_76 = lean_mk_string_unchecked("lib", 3, 3);
x_77 = lean_mk_string_unchecked("include", 7, 7);
x_78 = lean_mk_string_unchecked("bin", 3, 3);
lean_inc(x_42);
x_79 = l_Lake_leanSharedLibDir(x_42);
x_80 = l_Lake_leanSharedLib;
x_81 = l_Lake_initSharedLib;
x_82 = l_Lean_Compiler_FFI_getCFlags_x27;
x_83 = lean_mk_string_unchecked("-Wno-unused-command-line-argument", 33, 33);
x_84 = lean_box(0);
x_85 = l_Lake_findLeanInstall_x3f(x_47);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_mk_string_unchecked("", 0, 0);
x_89 = l_System_FilePath_join(x_74, x_75);
lean_inc(x_42);
x_90 = l_System_FilePath_join(x_42, x_76);
lean_dec(x_76);
lean_inc(x_90);
x_91 = l_System_FilePath_join(x_90, x_75);
lean_dec(x_75);
lean_inc(x_42);
x_92 = l_System_FilePath_join(x_42, x_77);
lean_dec(x_77);
lean_inc(x_42);
x_93 = l_System_FilePath_join(x_42, x_78);
lean_dec(x_78);
lean_inc(x_42);
x_94 = l_Lake_leanExe(x_42);
lean_inc(x_42);
x_95 = l_Lake_leancExe(x_42);
lean_inc(x_79);
x_96 = l_System_FilePath_join(x_79, x_80);
x_97 = l_System_FilePath_join(x_79, x_81);
x_98 = lean_mk_string_unchecked("ar", 2, 2);
x_99 = lean_mk_string_unchecked("cc", 2, 2);
x_100 = lean_array_push(x_82, x_83);
x_101 = lean_unbox(x_71);
x_102 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_101);
x_103 = lean_unbox(x_84);
x_104 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_103);
lean_inc(x_104);
lean_inc(x_102);
lean_inc(x_100);
x_105 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_105, 0, x_42);
lean_ctor_set(x_105, 1, x_88);
lean_ctor_set(x_105, 2, x_89);
lean_ctor_set(x_105, 3, x_91);
lean_ctor_set(x_105, 4, x_92);
lean_ctor_set(x_105, 5, x_90);
lean_ctor_set(x_105, 6, x_93);
lean_ctor_set(x_105, 7, x_94);
lean_ctor_set(x_105, 8, x_95);
lean_ctor_set(x_105, 9, x_96);
lean_ctor_set(x_105, 10, x_97);
lean_ctor_set(x_105, 11, x_98);
lean_ctor_set(x_105, 12, x_99);
lean_ctor_set(x_105, 13, x_100);
lean_ctor_set(x_105, 14, x_102);
lean_ctor_set(x_105, 15, x_104);
lean_ctor_set(x_105, 16, x_100);
lean_ctor_set(x_105, 17, x_102);
lean_ctor_set(x_105, 18, x_104);
x_106 = lean_unbox(x_71);
lean_dec(x_71);
lean_ctor_set_uint8(x_105, sizeof(void*)*19, x_106);
x_107 = l_Lake_LakeInstall_ofLean(x_105);
lean_ctor_set(x_69, 0, x_107);
lean_ctor_set(x_2, 1, x_69);
lean_ctor_set(x_2, 0, x_87);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_4);
lean_ctor_set(x_108, 1, x_2);
lean_ctor_set(x_85, 0, x_108);
return x_85;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_109 = lean_ctor_get(x_85, 0);
x_110 = lean_ctor_get(x_85, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_85);
x_111 = lean_mk_string_unchecked("", 0, 0);
x_112 = l_System_FilePath_join(x_74, x_75);
lean_inc(x_42);
x_113 = l_System_FilePath_join(x_42, x_76);
lean_dec(x_76);
lean_inc(x_113);
x_114 = l_System_FilePath_join(x_113, x_75);
lean_dec(x_75);
lean_inc(x_42);
x_115 = l_System_FilePath_join(x_42, x_77);
lean_dec(x_77);
lean_inc(x_42);
x_116 = l_System_FilePath_join(x_42, x_78);
lean_dec(x_78);
lean_inc(x_42);
x_117 = l_Lake_leanExe(x_42);
lean_inc(x_42);
x_118 = l_Lake_leancExe(x_42);
lean_inc(x_79);
x_119 = l_System_FilePath_join(x_79, x_80);
x_120 = l_System_FilePath_join(x_79, x_81);
x_121 = lean_mk_string_unchecked("ar", 2, 2);
x_122 = lean_mk_string_unchecked("cc", 2, 2);
x_123 = lean_array_push(x_82, x_83);
x_124 = lean_unbox(x_71);
x_125 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_124);
x_126 = lean_unbox(x_84);
x_127 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_126);
lean_inc(x_127);
lean_inc(x_125);
lean_inc(x_123);
x_128 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_128, 0, x_42);
lean_ctor_set(x_128, 1, x_111);
lean_ctor_set(x_128, 2, x_112);
lean_ctor_set(x_128, 3, x_114);
lean_ctor_set(x_128, 4, x_115);
lean_ctor_set(x_128, 5, x_113);
lean_ctor_set(x_128, 6, x_116);
lean_ctor_set(x_128, 7, x_117);
lean_ctor_set(x_128, 8, x_118);
lean_ctor_set(x_128, 9, x_119);
lean_ctor_set(x_128, 10, x_120);
lean_ctor_set(x_128, 11, x_121);
lean_ctor_set(x_128, 12, x_122);
lean_ctor_set(x_128, 13, x_123);
lean_ctor_set(x_128, 14, x_125);
lean_ctor_set(x_128, 15, x_127);
lean_ctor_set(x_128, 16, x_123);
lean_ctor_set(x_128, 17, x_125);
lean_ctor_set(x_128, 18, x_127);
x_129 = lean_unbox(x_71);
lean_dec(x_71);
lean_ctor_set_uint8(x_128, sizeof(void*)*19, x_129);
x_130 = l_Lake_LakeInstall_ofLean(x_128);
lean_ctor_set(x_69, 0, x_130);
lean_ctor_set(x_2, 1, x_69);
lean_ctor_set(x_2, 0, x_109);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_4);
lean_ctor_set(x_131, 1, x_2);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_110);
return x_132;
}
}
}
else
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_69, 0);
lean_inc(x_133);
lean_dec(x_69);
x_134 = lean_unbox(x_133);
if (x_134 == 0)
{
lean_dec(x_133);
lean_free_object(x_2);
goto block_67;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_41);
x_135 = lean_mk_string_unchecked("src", 3, 3);
lean_inc(x_42);
x_136 = l_System_FilePath_join(x_42, x_135);
lean_dec(x_135);
x_137 = lean_mk_string_unchecked("lean", 4, 4);
x_138 = lean_mk_string_unchecked("lib", 3, 3);
x_139 = lean_mk_string_unchecked("include", 7, 7);
x_140 = lean_mk_string_unchecked("bin", 3, 3);
lean_inc(x_42);
x_141 = l_Lake_leanSharedLibDir(x_42);
x_142 = l_Lake_leanSharedLib;
x_143 = l_Lake_initSharedLib;
x_144 = l_Lean_Compiler_FFI_getCFlags_x27;
x_145 = lean_mk_string_unchecked("-Wno-unused-command-line-argument", 33, 33);
x_146 = lean_box(0);
x_147 = l_Lake_findLeanInstall_x3f(x_47);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_mk_string_unchecked("", 0, 0);
x_152 = l_System_FilePath_join(x_136, x_137);
lean_inc(x_42);
x_153 = l_System_FilePath_join(x_42, x_138);
lean_dec(x_138);
lean_inc(x_153);
x_154 = l_System_FilePath_join(x_153, x_137);
lean_dec(x_137);
lean_inc(x_42);
x_155 = l_System_FilePath_join(x_42, x_139);
lean_dec(x_139);
lean_inc(x_42);
x_156 = l_System_FilePath_join(x_42, x_140);
lean_dec(x_140);
lean_inc(x_42);
x_157 = l_Lake_leanExe(x_42);
lean_inc(x_42);
x_158 = l_Lake_leancExe(x_42);
lean_inc(x_141);
x_159 = l_System_FilePath_join(x_141, x_142);
x_160 = l_System_FilePath_join(x_141, x_143);
x_161 = lean_mk_string_unchecked("ar", 2, 2);
x_162 = lean_mk_string_unchecked("cc", 2, 2);
x_163 = lean_array_push(x_144, x_145);
x_164 = lean_unbox(x_133);
x_165 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_164);
x_166 = lean_unbox(x_146);
x_167 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_166);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_163);
x_168 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_168, 0, x_42);
lean_ctor_set(x_168, 1, x_151);
lean_ctor_set(x_168, 2, x_152);
lean_ctor_set(x_168, 3, x_154);
lean_ctor_set(x_168, 4, x_155);
lean_ctor_set(x_168, 5, x_153);
lean_ctor_set(x_168, 6, x_156);
lean_ctor_set(x_168, 7, x_157);
lean_ctor_set(x_168, 8, x_158);
lean_ctor_set(x_168, 9, x_159);
lean_ctor_set(x_168, 10, x_160);
lean_ctor_set(x_168, 11, x_161);
lean_ctor_set(x_168, 12, x_162);
lean_ctor_set(x_168, 13, x_163);
lean_ctor_set(x_168, 14, x_165);
lean_ctor_set(x_168, 15, x_167);
lean_ctor_set(x_168, 16, x_163);
lean_ctor_set(x_168, 17, x_165);
lean_ctor_set(x_168, 18, x_167);
x_169 = lean_unbox(x_133);
lean_dec(x_133);
lean_ctor_set_uint8(x_168, sizeof(void*)*19, x_169);
x_170 = l_Lake_LakeInstall_ofLean(x_168);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_2, 1, x_171);
lean_ctor_set(x_2, 0, x_148);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_4);
lean_ctor_set(x_172, 1, x_2);
if (lean_is_scalar(x_150)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_150;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_149);
return x_173;
}
}
}
}
block_67:
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_box(1);
x_50 = lean_unbox(x_49);
x_51 = l_Lake_LeanInstall_get(x_42, x_50, x_47);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = l_Lake_LakeInstall_ofLean(x_53);
if (lean_is_scalar(x_43)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_43;
}
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
if (lean_is_scalar(x_48)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_48;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_41)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_41;
}
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_51, 0, x_58);
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
lean_inc(x_59);
x_61 = l_Lake_LakeInstall_ofLean(x_59);
if (lean_is_scalar(x_43)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_43;
}
lean_ctor_set(x_62, 0, x_59);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_61);
if (lean_is_scalar(x_48)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_48;
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_41)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_41;
}
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_2, 0);
x_175 = lean_ctor_get(x_2, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_2);
x_176 = l_Lake_findLakeLeanJointHome_x3f(x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = l_Lake_findLeanInstall_x3f(x_178);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = l_Lake_findLakeInstall_x3f(x_182);
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
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_183;
}
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_185);
if (lean_is_scalar(x_179)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_179;
}
lean_ctor_set(x_189, 0, x_174);
lean_ctor_set(x_189, 1, x_188);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_187;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_186);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_192 = x_176;
} else {
 lean_dec_ref(x_176);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_177, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_194 = x_177;
} else {
 lean_dec_ref(x_177);
 x_194 = lean_box(0);
}
x_195 = lean_mk_string_unchecked("LAKE_OVERRIDE_LEAN", 18, 18);
x_196 = lean_io_getenv(x_195, x_191);
lean_dec(x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
if (lean_obj_tag(x_197) == 0)
{
goto block_212;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_197, 0);
lean_inc(x_213);
lean_dec(x_197);
x_214 = l_Lake_envToBool_x3f(x_213);
if (lean_obj_tag(x_214) == 0)
{
goto block_212;
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
x_217 = lean_unbox(x_215);
if (x_217 == 0)
{
lean_dec(x_216);
lean_dec(x_215);
goto block_212;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_199);
lean_dec(x_194);
lean_dec(x_192);
x_218 = lean_mk_string_unchecked("src", 3, 3);
lean_inc(x_193);
x_219 = l_System_FilePath_join(x_193, x_218);
lean_dec(x_218);
x_220 = lean_mk_string_unchecked("lean", 4, 4);
x_221 = lean_mk_string_unchecked("lib", 3, 3);
x_222 = lean_mk_string_unchecked("include", 7, 7);
x_223 = lean_mk_string_unchecked("bin", 3, 3);
lean_inc(x_193);
x_224 = l_Lake_leanSharedLibDir(x_193);
x_225 = l_Lake_leanSharedLib;
x_226 = l_Lake_initSharedLib;
x_227 = l_Lean_Compiler_FFI_getCFlags_x27;
x_228 = lean_mk_string_unchecked("-Wno-unused-command-line-argument", 33, 33);
x_229 = lean_box(0);
x_230 = l_Lake_findLeanInstall_x3f(x_198);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_mk_string_unchecked("", 0, 0);
x_235 = l_System_FilePath_join(x_219, x_220);
lean_inc(x_193);
x_236 = l_System_FilePath_join(x_193, x_221);
lean_dec(x_221);
lean_inc(x_236);
x_237 = l_System_FilePath_join(x_236, x_220);
lean_dec(x_220);
lean_inc(x_193);
x_238 = l_System_FilePath_join(x_193, x_222);
lean_dec(x_222);
lean_inc(x_193);
x_239 = l_System_FilePath_join(x_193, x_223);
lean_dec(x_223);
lean_inc(x_193);
x_240 = l_Lake_leanExe(x_193);
lean_inc(x_193);
x_241 = l_Lake_leancExe(x_193);
lean_inc(x_224);
x_242 = l_System_FilePath_join(x_224, x_225);
x_243 = l_System_FilePath_join(x_224, x_226);
x_244 = lean_mk_string_unchecked("ar", 2, 2);
x_245 = lean_mk_string_unchecked("cc", 2, 2);
x_246 = lean_array_push(x_227, x_228);
x_247 = lean_unbox(x_215);
x_248 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_247);
x_249 = lean_unbox(x_229);
x_250 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_249);
lean_inc(x_250);
lean_inc(x_248);
lean_inc(x_246);
x_251 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_251, 0, x_193);
lean_ctor_set(x_251, 1, x_234);
lean_ctor_set(x_251, 2, x_235);
lean_ctor_set(x_251, 3, x_237);
lean_ctor_set(x_251, 4, x_238);
lean_ctor_set(x_251, 5, x_236);
lean_ctor_set(x_251, 6, x_239);
lean_ctor_set(x_251, 7, x_240);
lean_ctor_set(x_251, 8, x_241);
lean_ctor_set(x_251, 9, x_242);
lean_ctor_set(x_251, 10, x_243);
lean_ctor_set(x_251, 11, x_244);
lean_ctor_set(x_251, 12, x_245);
lean_ctor_set(x_251, 13, x_246);
lean_ctor_set(x_251, 14, x_248);
lean_ctor_set(x_251, 15, x_250);
lean_ctor_set(x_251, 16, x_246);
lean_ctor_set(x_251, 17, x_248);
lean_ctor_set(x_251, 18, x_250);
x_252 = lean_unbox(x_215);
lean_dec(x_215);
lean_ctor_set_uint8(x_251, sizeof(void*)*19, x_252);
x_253 = l_Lake_LakeInstall_ofLean(x_251);
if (lean_is_scalar(x_216)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_216;
}
lean_ctor_set(x_254, 0, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_231);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_174);
lean_ctor_set(x_256, 1, x_255);
if (lean_is_scalar(x_233)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_233;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_232);
return x_257;
}
}
}
block_212:
{
lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_200 = lean_box(1);
x_201 = lean_unbox(x_200);
x_202 = l_Lake_LeanInstall_get(x_193, x_201, x_198);
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
lean_inc(x_203);
x_206 = l_Lake_LakeInstall_ofLean(x_203);
if (lean_is_scalar(x_194)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_194;
}
lean_ctor_set(x_207, 0, x_203);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_206);
if (lean_is_scalar(x_199)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_199;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
if (lean_is_scalar(x_192)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_192;
}
lean_ctor_set(x_210, 0, x_174);
lean_ctor_set(x_210, 1, x_209);
if (lean_is_scalar(x_205)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_205;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_204);
return x_211;
}
}
}
}
}
lean_object* initialize_Init_Control_Option(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_FFI(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_FFI(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedElanInstall = _init_l_Lake_instInhabitedElanInstall();
lean_mark_persistent(l_Lake_instInhabitedElanInstall);
l_Lake_instReprElanInstall = _init_l_Lake_instReprElanInstall();
lean_mark_persistent(l_Lake_instReprElanInstall);
l_Lake_leanSharedLib = _init_l_Lake_leanSharedLib();
lean_mark_persistent(l_Lake_leanSharedLib);
l_Lake_initSharedLib = _init_l_Lake_initSharedLib();
lean_mark_persistent(l_Lake_initSharedLib);
l_Lake_instInhabitedLeanInstall = _init_l_Lake_instInhabitedLeanInstall();
lean_mark_persistent(l_Lake_instInhabitedLeanInstall);
l_Lake_instReprLeanInstall = _init_l_Lake_instReprLeanInstall();
lean_mark_persistent(l_Lake_instReprLeanInstall);
l_Lake_lakeExe = _init_l_Lake_lakeExe();
lean_mark_persistent(l_Lake_lakeExe);
l_Lake_instInhabitedLakeInstall = _init_l_Lake_instInhabitedLakeInstall();
lean_mark_persistent(l_Lake_instInhabitedLakeInstall);
l_Lake_instReprLakeInstall = _init_l_Lake_instReprLakeInstall();
lean_mark_persistent(l_Lake_instReprLakeInstall);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
