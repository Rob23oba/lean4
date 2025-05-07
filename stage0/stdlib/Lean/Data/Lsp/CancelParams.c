// Lean compiler output
// Module: Lean.Data.Lsp.CancelParams
// Imports: Lean.Data.JsonRpc
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCancelParams;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_86_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqCancelParams;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_beqCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_28____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams___lam__0____x40_Lean_Data_Lsp_CancelParams___hyg_124____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams___lam__0____x40_Lean_Data_Lsp_CancelParams___hyg_124_(lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_beqCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_28_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_124_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCancelParams;
lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_86__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedCancelParams;
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Lsp_instInhabitedCancelParams() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_beqCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_28_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_beqCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_28____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_beqCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_28_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqCancelParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_beqCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_28____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_86__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_86_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_ctor_set_tag(x_1, 3);
x_3 = x_1;
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_3 = x_16;
goto block_13;
}
}
case 1:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_ctor_set_tag(x_1, 2);
x_3 = x_1;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_3 = x_19;
goto block_13;
}
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
x_3 = x_20;
goto block_13;
}
}
block_13:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
x_11 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_86__spec__0(x_8, x_10);
x_12 = l_Lean_Json_mkObj(x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonCancelParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_86_), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams___lam__0____x40_Lean_Data_Lsp_CancelParams___hyg_124_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_124_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("id", 2, 2);
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams___lam__0____x40_Lean_Data_Lsp_CancelParams___hyg_124____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("CancelParams", 12, 12);
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
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams___lam__0____x40_Lean_Data_Lsp_CancelParams___hyg_124____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("CancelParams", 12, 12);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams___lam__0____x40_Lean_Data_Lsp_CancelParams___hyg_124____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams___lam__0____x40_Lean_Data_Lsp_CancelParams___hyg_124_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCancelParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_CancelParams_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_CancelParams___hyg_124_), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_CancelParams(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_JsonRpc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedCancelParams = _init_l_Lean_Lsp_instInhabitedCancelParams();
lean_mark_persistent(l_Lean_Lsp_instInhabitedCancelParams);
l_Lean_Lsp_instBEqCancelParams = _init_l_Lean_Lsp_instBEqCancelParams();
lean_mark_persistent(l_Lean_Lsp_instBEqCancelParams);
l_Lean_Lsp_instToJsonCancelParams = _init_l_Lean_Lsp_instToJsonCancelParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonCancelParams);
l_Lean_Lsp_instFromJsonCancelParams = _init_l_Lean_Lsp_instFromJsonCancelParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonCancelParams);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
