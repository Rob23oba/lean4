// Lean compiler output
// Module: Lake.Config.WorkspaceConfig
// Imports: Lake.Config.Meta Lake.Config.Defaults
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
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instEmptyCollectionWorkspaceConfig;
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultPackagesDir;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__2(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedWorkspaceConfig;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig___redArg____x40_Lake_Config_WorkspaceConfig___hyg_32_(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigFields;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig___redArg____x40_Lake_Config_WorkspaceConfig___hyg_32____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig___fields;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigMeta___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprWorkspaceConfig;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig____x40_Lake_Config_WorkspaceConfig___hyg_32____boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir_instConfigField;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigMeta;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig____x40_Lake_Config_WorkspaceConfig___hyg_32_(lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedWorkspaceConfig() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig___redArg____x40_Lake_Config_WorkspaceConfig___hyg_32_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("packagesDir", 11, 11);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(15u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_String_quote(x_1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_12);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_mk_string_unchecked(" }", 2, 2);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unbox(x_20);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
return x_32;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig____x40_Lake_Config_WorkspaceConfig___hyg_32_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig___redArg____x40_Lake_Config_WorkspaceConfig___hyg_32_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig___redArg____x40_Lake_Config_WorkspaceConfig___hyg_32____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig___redArg____x40_Lake_Config_WorkspaceConfig___hyg_32_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig____x40_Lake_Config_WorkspaceConfig___hyg_32____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig____x40_Lake_Config_WorkspaceConfig___hyg_32_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprWorkspaceConfig() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_WorkspaceConfig_0__Lake_reprWorkspaceConfig____x40_Lake_Config_WorkspaceConfig___hyg_32____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultPackagesDir;
return x_2;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_packagesDir___proj() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_alloc_closure((void*)(l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed), 2, 0);
x_3 = lean_alloc_closure((void*)(l_Lake_WorkspaceConfig_packagesDir___proj___lam__2), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed), 1, 0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_WorkspaceConfig_packagesDir___proj___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_WorkspaceConfig_packagesDir___proj___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_packagesDir___proj___lam__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_WorkspaceConfig_packagesDir___proj___lam__3(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_packagesDir_instConfigField() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_WorkspaceConfig_packagesDir___proj;
return x_1;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig___fields() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_1 = l_Array_empty(lean_box(0));
x_2 = lean_mk_string_unchecked("packagesDir", 11, 11);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_8);
x_9 = lean_array_push(x_1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigFields() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_WorkspaceConfig___fields;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_instConfigMeta___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_instConfigMeta() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_1 = l_Lake_WorkspaceConfig___fields;
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_nat_dec_lt(x_3, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_4, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_alloc_closure((void*)(l_Lake_WorkspaceConfig_instConfigMeta___lam__0), 2, 0);
x_20 = lean_usize_of_nat(x_3);
x_21 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_22 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_14, x_19, x_1, x_20, x_21, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lake_instEmptyCollectionWorkspaceConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultPackagesDir;
return x_1;
}
}
lean_object* initialize_Lake_Config_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_WorkspaceConfig(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedWorkspaceConfig = _init_l_Lake_instInhabitedWorkspaceConfig();
lean_mark_persistent(l_Lake_instInhabitedWorkspaceConfig);
l_Lake_instReprWorkspaceConfig = _init_l_Lake_instReprWorkspaceConfig();
lean_mark_persistent(l_Lake_instReprWorkspaceConfig);
l_Lake_WorkspaceConfig_packagesDir___proj = _init_l_Lake_WorkspaceConfig_packagesDir___proj();
lean_mark_persistent(l_Lake_WorkspaceConfig_packagesDir___proj);
l_Lake_WorkspaceConfig_packagesDir_instConfigField = _init_l_Lake_WorkspaceConfig_packagesDir_instConfigField();
lean_mark_persistent(l_Lake_WorkspaceConfig_packagesDir_instConfigField);
l_Lake_WorkspaceConfig___fields = _init_l_Lake_WorkspaceConfig___fields();
lean_mark_persistent(l_Lake_WorkspaceConfig___fields);
l_Lake_WorkspaceConfig_instConfigFields = _init_l_Lake_WorkspaceConfig_instConfigFields();
lean_mark_persistent(l_Lake_WorkspaceConfig_instConfigFields);
l_Lake_WorkspaceConfig_instConfigMeta = _init_l_Lake_WorkspaceConfig_instConfigMeta();
lean_mark_persistent(l_Lake_WorkspaceConfig_instConfigMeta);
l_Lake_instEmptyCollectionWorkspaceConfig = _init_l_Lake_instEmptyCollectionWorkspaceConfig();
lean_mark_persistent(l_Lake_instEmptyCollectionWorkspaceConfig);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
