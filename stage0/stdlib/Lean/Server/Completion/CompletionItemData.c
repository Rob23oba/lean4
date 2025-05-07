// Lean compiler output
// Module: Lean.Server.Completion.CompletionItemData
// Imports: Lean.Server.FileSource
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
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3059_(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionItem;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Window_0__toJsonShowMessageParams____x40_Lean_Data_Lsp_Window___hyg_245__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2953_(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionItemData;
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionItemData;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_15_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2953_(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_15_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("params", 6, 6);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_15____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("CompletionItemData", 18, 18);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_15____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("CompletionItemData", 18, 18);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_15____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_15_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("params", 6, 6);
x_3 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3059_(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Window_0__toJsonShowMessageParams____x40_Lean_Data_Lsp_Window___hyg_245__spec__0(x_8, x_10);
x_12 = l_Lean_Json_mkObj(x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_82_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_mk_string_unchecked("no data param on completion item ", 33, 33);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_2 = x_13;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l___private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15_(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_2 = x_16;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
block_9:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_mk_string_unchecked("Lean.Server.Completion.CompletionItemData", 41, 41);
x_4 = lean_mk_string_unchecked("Lean.Lsp.CompletionItem.getFileSource!", 38, 38);
x_5 = lean_unsigned_to_nat(34u);
x_6 = lean_unsigned_to_nat(22u);
x_7 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_2);
lean_dec(x_2);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_panic___at___Lean_Name_getString_x21_spec__0(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionItem() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_getFileSource_x21), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Server_FileSource(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionItemData(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_FileSource(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instFromJsonCompletionItemData = _init_l_Lean_Lsp_instFromJsonCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instFromJsonCompletionItemData);
l_Lean_Lsp_instToJsonCompletionItemData = _init_l_Lean_Lsp_instToJsonCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instToJsonCompletionItemData);
l_Lean_Lsp_instFileSourceCompletionItem = _init_l_Lean_Lsp_instFileSourceCompletionItem();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionItem);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
