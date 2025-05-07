// Lean compiler output
// Module: Lean.Widget.Types
// Imports: Lean.Server.Rpc.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261_(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_enc____x40_Lean_Widget_Types___hyg_3_(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_324_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261____boxed(lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_enc___lam__0____x40_Lean_Widget_Types___hyg_3____boxed(lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg___lam__0____x40_Lean_Widget_Types___hyg_3_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg____x40_Lean_Widget_Types___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Widget_instRpcEncodableWidgetInstance_enc___lam__0____x40_Lean_Widget_Types___hyg_3_(lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_258_;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_mk_string_unchecked("id", 2, 2);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("javascriptHash", 14, 14);
lean_inc(x_1);
x_6 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(x_1, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("props", 5, 5);
x_9 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(x_1, x_8);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_258_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_mk_string_unchecked("id", 2, 2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("javascriptHash", 14, 14);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_mk_string_unchecked("props", 5, 5);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = l_List_flatMapTR_go___at_____private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173__spec__0(x_18, x_20);
x_22 = l_Lean_Json_mkObj(x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_324_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Widget_instRpcEncodableWidgetInstance_enc___lam__0____x40_Lean_Widget_Types___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_enc____x40_Lean_Widget_Types___hyg_3_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_apply_1(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableWidgetInstance_enc___lam__0____x40_Lean_Widget_Types___hyg_3____boxed), 1, 0);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_box(1);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_Name_toString(x_8, x_11, x_7);
x_13 = lean_uint64_to_nat(x_10);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_bignumToJson(x_13);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_6);
x_17 = l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261_(x_16);
lean_dec(x_16);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableWidgetInstance_enc___lam__0____x40_Lean_Widget_Types___hyg_3____boxed), 1, 0);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_box(1);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_24 = lean_unbox(x_22);
x_25 = l_Lean_Name_toString(x_21, x_24, x_20);
x_26 = lean_uint64_to_nat(x_23);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = l_Lean_bignumToJson(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_18);
x_30 = l___private_Lean_Widget_Types_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_261_(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_enc___lam__0____x40_Lean_Widget_Types___hyg_3____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Widget_instRpcEncodableWidgetInstance_enc___lam__0____x40_Lean_Widget_Types___hyg_3_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg___lam__0____x40_Lean_Widget_Types___hyg_3_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg____x40_Lean_Widget_Types___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_30; lean_object* x_31; 
x_2 = l___private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
lean_inc(x_30);
x_31 = l_Lean_Json_getStr_x3f(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_30);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_38 = lean_string_dec_eq(x_36, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_String_toName(x_36);
x_40 = l_Lean_Name_isAnonymous(x_39);
if (x_40 == 0)
{
lean_free_object(x_31);
lean_dec(x_30);
x_4 = x_39;
goto block_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
lean_dec(x_3);
x_41 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_42 = lean_unsigned_to_nat(80u);
x_43 = l_Lean_Json_pretty(x_30, x_42);
x_44 = lean_string_append(x_41, x_43);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked("'", 1, 1);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_46);
return x_31;
}
}
else
{
lean_object* x_47; 
lean_free_object(x_31);
lean_dec(x_36);
lean_dec(x_30);
x_47 = lean_box(0);
x_4 = x_47;
goto block_29;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_50 = lean_string_dec_eq(x_48, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_String_toName(x_48);
x_52 = l_Lean_Name_isAnonymous(x_51);
if (x_52 == 0)
{
lean_dec(x_30);
x_4 = x_51;
goto block_29;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_51);
lean_dec(x_3);
x_53 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_54 = lean_unsigned_to_nat(80u);
x_55 = l_Lean_Json_pretty(x_30, x_54);
x_56 = lean_string_append(x_53, x_55);
lean_dec(x_55);
x_57 = lean_mk_string_unchecked("'", 1, 1);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_dec(x_48);
lean_dec(x_30);
x_60 = lean_box(0);
x_4 = x_60;
goto block_29;
}
}
}
block_29:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_bignumFromJson_x3f(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_cstr_to_nat("18446744073709551616");
x_13 = lean_nat_dec_le(x_12, x_11);
lean_dec(x_12);
if (x_13 == 0)
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_uint64_of_nat(x_11);
lean_dec(x_11);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg___lam__0____x40_Lean_Widget_Types___hyg_3_), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint64(x_17, sizeof(void*)*2, x_14);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
else
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_cstr_to_nat("18446744073709551616");
x_21 = lean_nat_dec_le(x_20, x_19);
lean_dec(x_20);
if (x_21 == 0)
{
uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_uint64_of_nat(x_19);
lean_dec(x_19);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg___lam__0____x40_Lean_Widget_Types___hyg_3_), 2, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg____x40_Lean_Widget_Types___hyg_3_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_MonadExcept_ofExcept___at___Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3__spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableWidgetInstance() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableWidgetInstance_enc____x40_Lean_Widget_Types___hyg_3_), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableWidgetInstance_dec____x40_Lean_Widget_Types___hyg_3____boxed), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_258_ = _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_258_();
lean_mark_persistent(l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_258_);
l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_324_ = _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_324_();
lean_mark_persistent(l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_324_);
l_Lean_Widget_instRpcEncodableWidgetInstance = _init_l_Lean_Widget_instRpcEncodableWidgetInstance();
lean_mark_persistent(l_Lean_Widget_instRpcEncodableWidgetInstance);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
