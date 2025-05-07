// Lean compiler output
// Module: Lake.Config.Kinds
// Imports: Init.Prelude
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
LEAN_EXPORT lean_object* l_Lake_InputFile_keyword;
LEAN_EXPORT lean_object* l_Lake_LeanLib_keyword;
LEAN_EXPORT lean_object* l_Lake_Package_keyword;
LEAN_EXPORT lean_object* l_Lake_facetKindForNamespace(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_facetKind;
LEAN_EXPORT lean_object* l_Lake_InputDir_configKind;
LEAN_EXPORT lean_object* l_Lake_LeanExe_configKind;
LEAN_EXPORT lean_object* l_Lake_Module_facetKind;
LEAN_EXPORT lean_object* l_Lake_LeanExe_facetKind;
LEAN_EXPORT lean_object* l_Lake_facetKindForNamespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_configKind;
LEAN_EXPORT lean_object* l_Lake_LeanLib_facetKind;
LEAN_EXPORT lean_object* l_Lake_InputDir_facetKind;
LEAN_EXPORT lean_object* l_Lake_InputFile_configKind;
LEAN_EXPORT lean_object* l_Lake_ExternLib_facetKind;
LEAN_EXPORT lean_object* l_Lake_Module_keyword;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_keyword;
LEAN_EXPORT lean_object* l_Lake_LeanLib_configKind;
LEAN_EXPORT lean_object* l_Lake_LeanExe_keyword;
LEAN_EXPORT lean_object* l_Lake_InputFile_facetKind;
LEAN_EXPORT lean_object* l_Lake_ExternLib_keyword;
static lean_object* _init_l_Lake_Package_keyword() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_facetKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_Module_keyword() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Module_facetKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Module_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLib_keyword() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_facetKind() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLib_configKind() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanExe_keyword() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("lean_exe", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanExe_facetKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanExe_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExe_configKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanExe_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_keyword() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("extern_lib", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_ExternLib_facetKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ExternLib_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_ExternLib_configKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_ExternLib_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_InputFile_keyword() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("input_file", 10, 10);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InputFile_facetKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_InputFile_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_InputFile_configKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_InputFile_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_InputDir_keyword() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("input_dir", 9, 9);
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InputDir_facetKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_InputDir_keyword;
return x_1;
}
}
static lean_object* _init_l_Lake_InputDir_configKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_InputDir_keyword;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_facetKindForNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_mk_string_unchecked("Lake", 4, 4);
x_8 = lean_string_dec_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
return x_2;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_mk_string_unchecked("Package", 7, 7);
x_10 = lean_string_dec_eq(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_mk_string_unchecked("Module", 6, 6);
x_12 = lean_string_dec_eq(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_mk_string_unchecked("LeanLib", 7, 7);
x_14 = lean_string_dec_eq(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_mk_string_unchecked("LeanExe", 7, 7);
x_16 = lean_string_dec_eq(x_4, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_mk_string_unchecked("ExternLib", 9, 9);
x_18 = lean_string_dec_eq(x_4, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_mk_string_unchecked("InputFile", 9, 9);
x_20 = lean_string_dec_eq(x_4, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_mk_string_unchecked("InputDir", 8, 8);
x_22 = lean_string_dec_eq(x_4, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
return x_2;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_23; 
x_23 = l_Lake_InputDir_keyword;
return x_23;
}
else
{
return x_2;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_24; 
x_24 = l_Lake_InputFile_keyword;
return x_24;
}
else
{
return x_2;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_25; 
x_25 = l_Lake_ExternLib_keyword;
return x_25;
}
else
{
return x_2;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_26; 
x_26 = l_Lake_LeanExe_keyword;
return x_26;
}
else
{
return x_2;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_28 = l_Lean_Name_mkStr1(x_27);
return x_28;
}
else
{
return x_2;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_29; 
x_29 = l_Lake_Module_keyword;
return x_29;
}
else
{
return x_2;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_30; 
x_30 = l_Lake_Package_keyword;
return x_30;
}
else
{
return x_2;
}
}
}
}
else
{
return x_2;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_facetKindForNamespace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_facetKindForNamespace(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Kinds(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Package_keyword = _init_l_Lake_Package_keyword();
lean_mark_persistent(l_Lake_Package_keyword);
l_Lake_Package_facetKind = _init_l_Lake_Package_facetKind();
lean_mark_persistent(l_Lake_Package_facetKind);
l_Lake_Module_keyword = _init_l_Lake_Module_keyword();
lean_mark_persistent(l_Lake_Module_keyword);
l_Lake_Module_facetKind = _init_l_Lake_Module_facetKind();
lean_mark_persistent(l_Lake_Module_facetKind);
l_Lake_LeanLib_keyword = _init_l_Lake_LeanLib_keyword();
lean_mark_persistent(l_Lake_LeanLib_keyword);
l_Lake_LeanLib_facetKind = _init_l_Lake_LeanLib_facetKind();
lean_mark_persistent(l_Lake_LeanLib_facetKind);
l_Lake_LeanLib_configKind = _init_l_Lake_LeanLib_configKind();
lean_mark_persistent(l_Lake_LeanLib_configKind);
l_Lake_LeanExe_keyword = _init_l_Lake_LeanExe_keyword();
lean_mark_persistent(l_Lake_LeanExe_keyword);
l_Lake_LeanExe_facetKind = _init_l_Lake_LeanExe_facetKind();
lean_mark_persistent(l_Lake_LeanExe_facetKind);
l_Lake_LeanExe_configKind = _init_l_Lake_LeanExe_configKind();
lean_mark_persistent(l_Lake_LeanExe_configKind);
l_Lake_ExternLib_keyword = _init_l_Lake_ExternLib_keyword();
lean_mark_persistent(l_Lake_ExternLib_keyword);
l_Lake_ExternLib_facetKind = _init_l_Lake_ExternLib_facetKind();
lean_mark_persistent(l_Lake_ExternLib_facetKind);
l_Lake_ExternLib_configKind = _init_l_Lake_ExternLib_configKind();
lean_mark_persistent(l_Lake_ExternLib_configKind);
l_Lake_InputFile_keyword = _init_l_Lake_InputFile_keyword();
lean_mark_persistent(l_Lake_InputFile_keyword);
l_Lake_InputFile_facetKind = _init_l_Lake_InputFile_facetKind();
lean_mark_persistent(l_Lake_InputFile_facetKind);
l_Lake_InputFile_configKind = _init_l_Lake_InputFile_configKind();
lean_mark_persistent(l_Lake_InputFile_configKind);
l_Lake_InputDir_keyword = _init_l_Lake_InputDir_keyword();
lean_mark_persistent(l_Lake_InputDir_keyword);
l_Lake_InputDir_facetKind = _init_l_Lake_InputDir_facetKind();
lean_mark_persistent(l_Lake_InputDir_facetKind);
l_Lake_InputDir_configKind = _init_l_Lake_InputDir_configKind();
lean_mark_persistent(l_Lake_InputDir_configKind);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
