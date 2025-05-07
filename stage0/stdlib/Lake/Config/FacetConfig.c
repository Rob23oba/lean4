// Lean compiler output
// Module: Lake.Config.FacetConfig
// Imports: Lake.Build.Fetch Lake.Config.OutFormat
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
LEAN_EXPORT lean_object* l_Lake_instTypeNameLibraryFacetDecl;
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instTypeNameModuleFacetDecl;
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instTypeNamePackageFacetDecl;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_472_;
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_428_;
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_450_;
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___boxed(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name(lean_object*, lean_object*);
lean_object* l_Lake_OptDataKind_anonymous(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_kind__eq___autoParam;
lean_object* l_Lake_instInhabitedOptDataKind(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_box(0);
x_9 = l_Array_empty(lean_box(0));
x_10 = lean_box(0);
x_11 = lean_mk_string_unchecked("<nil>", 5, 5);
x_12 = l_Lake_BuildTrace_nil(x_11);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unbox(x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_14);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_task_pure(x_15);
x_17 = l_Lake_OptDataKind_anonymous(lean_box(0));
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("", 0, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_alloc_closure((void*)(l_Lake_instInhabitedFacetConfig___lam__0___boxed), 7, 0);
x_3 = lean_alloc_closure((void*)(l_Lake_instInhabitedFacetConfig___lam__1___boxed), 2, 0);
x_4 = l_Lake_instInhabitedOptDataKind(lean_box(0));
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_8);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_instInhabitedFacetConfig___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_instInhabitedFacetConfig___lam__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedFacetConfig(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_FacetConfig_name___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_FacetConfig_name(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = lean_mk_string_unchecked("rfl", 3, 3);
x_15 = l_Lean_mkAtom(x_14);
lean_inc(x_7);
x_16 = lean_array_push(x_7, x_15);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_inc(x_7);
x_18 = lean_array_push(x_7, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_18);
lean_inc(x_7);
x_20 = lean_array_push(x_7, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_9);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_push(x_7, x_21);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_FacetConfig_toKind___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_FacetConfig_toKind(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_name_eq(x_3, x_1);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_FacetConfig_toKind_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_FacetConfig_toKind_x3f___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_FacetConfig_toKind_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_7(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_apply_7(x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_KFacetConfig_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lake_mkFacetJobConfig___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Lake_mkFacetJobConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_428_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("ModuleFacetDecl", 15, 15);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instTypeNameModuleFacetDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_428_;
return x_1;
}
}
static lean_object* _init_l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_450_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("PackageFacetDecl", 16, 16);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instTypeNamePackageFacetDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_450_;
return x_1;
}
}
static lean_object* _init_l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_472_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("LibraryFacetDecl", 16, 16);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instTypeNameLibraryFacetDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_472_;
return x_1;
}
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_OutFormat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_OutFormat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_KFacetConfig_kind__eq___autoParam = _init_l_Lake_KFacetConfig_kind__eq___autoParam();
lean_mark_persistent(l_Lake_KFacetConfig_kind__eq___autoParam);
l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_428_ = _init_l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_428_();
lean_mark_persistent(l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_428_);
l_Lake_instTypeNameModuleFacetDecl = _init_l_Lake_instTypeNameModuleFacetDecl();
lean_mark_persistent(l_Lake_instTypeNameModuleFacetDecl);
l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_450_ = _init_l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_450_();
lean_mark_persistent(l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_450_);
l_Lake_instTypeNamePackageFacetDecl = _init_l_Lake_instTypeNamePackageFacetDecl();
lean_mark_persistent(l_Lake_instTypeNamePackageFacetDecl);
l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_472_ = _init_l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_472_();
lean_mark_persistent(l_Lake_instImpl____x40_Lake_Config_FacetConfig___hyg_472_);
l_Lake_instTypeNameLibraryFacetDecl = _init_l_Lake_instTypeNameLibraryFacetDecl();
lean_mark_persistent(l_Lake_instTypeNameLibraryFacetDecl);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
