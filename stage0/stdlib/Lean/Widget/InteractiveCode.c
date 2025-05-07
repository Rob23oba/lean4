// Lean compiler output
// Module: Lean.Widget.InteractiveCode
// Imports: Lean.Server.Rpc.Basic Lean.Server.InfoUtils Lean.Widget.TaggedText Lean.Widget.Basic
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
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__1____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_605_;
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc____x40_Lean_Widget_InteractiveCode___hyg_292_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_prettyTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__5____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__4____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_pretty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_raw;
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPInstantiateMVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__5____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instToJsonDiffTag;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552_(lean_object*);
lean_object* l_Lean_RBNode_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonDiffTag;
lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11_(uint8_t);
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_rewrite___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_549_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__0____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec____x40_Lean_Widget_InteractiveCode___hyg_292_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo;
lean_object* l_Lean_RBNode_find___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object*);
extern lean_object* l_instOrdNat;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__3____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__1____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg___lam__0(lean_object*);
lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__2____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__3____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__0____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__2____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Widget_instImpl____x40_Lean_Widget_Basic___hyg_5_;
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__4____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Widget_DiffTag_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Widget_DiffTag_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Widget_DiffTag_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Widget_DiffTag_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Widget_DiffTag_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_DiffTag_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Widget_DiffTag_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("wasChanged", 10, 10);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("willChange", 10, 10);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("wasDeleted", 10, 10);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_mk_string_unchecked("willDelete", 10, 10);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_mk_string_unchecked("wasInserted", 11, 11);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_mk_string_unchecked("willInsert", 10, 10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11_(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_instToJsonDiffTag() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__0____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__1____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("wasInserted", 11, 11);
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(4);
lean_ctor_set(x_7, 0, x_15);
x_16 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_box(4);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__2____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("willDelete", 10, 10);
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(3);
lean_ctor_set(x_7, 0, x_15);
x_16 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_box(3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__3____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("wasDeleted", 10, 10);
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(2);
lean_ctor_set(x_7, 0, x_15);
x_16 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__4____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("willChange", 10, 10);
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(1);
lean_ctor_set(x_7, 0, x_15);
x_16 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__5____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("wasChanged", 10, 10);
x_7 = l_Lean_Json_parseTagged(x_1, x_6, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Except_orElseLazy___redArg(x_11, x_4);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
x_16 = l_Except_orElseLazy___redArg(x_7, x_4);
lean_dec(x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Except_orElseLazy___redArg(x_18, x_4);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_68_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__0____x40_Lean_Widget_InteractiveCode___hyg_68____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("willInsert", 10, 10);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__1____x40_Lean_Widget_InteractiveCode___hyg_68____boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_2);
lean_inc(x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__2____x40_Lean_Widget_InteractiveCode___hyg_68____boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_7);
lean_inc(x_6);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__3____x40_Lean_Widget_InteractiveCode___hyg_68____boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_8);
lean_inc(x_6);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__4____x40_Lean_Widget_InteractiveCode___hyg_68____boxed), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_6);
lean_closure_set(x_10, 3, x_9);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__5____x40_Lean_Widget_InteractiveCode___hyg_68____boxed), 5, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_Json_parseTagged(x_1, x_3, x_4, x_6);
lean_dec(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Except_orElseLazy___redArg(x_12, x_11);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Except_orElseLazy___redArg(x_16, x_11);
lean_dec(x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(5);
lean_ctor_set(x_12, 0, x_20);
x_21 = l_Except_orElseLazy___redArg(x_12, x_11);
lean_dec(x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_22 = lean_box(5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Except_orElseLazy___redArg(x_23, x_11);
lean_dec(x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__0____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__0____x40_Lean_Widget_InteractiveCode___hyg_68_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__1____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__1____x40_Lean_Widget_InteractiveCode___hyg_68_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__2____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__2____x40_Lean_Widget_InteractiveCode___hyg_68_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__3____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__3____x40_Lean_Widget_InteractiveCode___hyg_68_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__4____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__4____x40_Lean_Widget_InteractiveCode___hyg_68_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__5____x40_Lean_Widget_InteractiveCode___hyg_68____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag___lam__5____x40_Lean_Widget_InteractiveCode___hyg_68_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonDiffTag() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_68_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_mk_string_unchecked("info", 4, 4);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(x_1, x_2);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("subexprPos", 10, 10);
lean_inc(x_1);
x_6 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_Types_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_Types___hyg_62__spec__0(x_1, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("diffStatus", 10, 10);
x_9 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_549_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("info", 4, 4);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("subexprPos", 10, 10);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_mk_string_unchecked("diffStatus", 10, 10);
x_12 = lean_ctor_get(x_1, 2);
x_13 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_11, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_17, x_19);
x_21 = l_Lean_Json_mkObj(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_____private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_605_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_enc____x40_Lean_Widget_InteractiveCode___hyg_292_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; 
x_3 = l_Lean_Widget_instImpl____x40_Lean_Widget_Basic___hyg_5_;
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_box(0), x_3, x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_SubExpr_Pos_toString(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_12 = x_18;
goto block_16;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11_(x_21);
lean_ctor_set(x_17, 0, x_22);
x_12 = x_17;
goto block_16;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
x_25 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_11_(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_12 = x_26;
goto block_16;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_toJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_552_(x_13);
lean_dec(x_13);
if (lean_is_scalar(x_8)) {
 x_15 = lean_alloc_ctor(0, 2, 0);
} else {
 x_15 = x_8;
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_instRpcEncodableSubexprInfo_dec____x40_Lean_Widget_InteractiveCode___hyg_292_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_353_(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Widget_instImpl____x40_Lean_Widget_Basic___hyg_5_;
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(x_5, x_6, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = l_Lean_Json_getStr_x3f(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_SubExpr_Pos_fromString_x3f(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
lean_dec(x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_24 = x_29;
goto block_27;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_68_(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_free_object(x_28);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
lean_ctor_set(x_28, 0, x_36);
x_24 = x_28;
goto block_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = l___private_Lean_Widget_InteractiveCode_0__Lean_Widget_fromJsonDiffTag____x40_Lean_Widget_InteractiveCode___hyg_68_(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_24 = x_43;
goto block_27;
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Widget_instRpcEncodableSubexprInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableSubexprInfo_enc____x40_Lean_Widget_InteractiveCode___hyg_292_), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Widget_instRpcEncodableSubexprInfo_dec____x40_Lean_Widget_InteractiveCode___hyg_292_), 2, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Lean_RBNode_find(lean_box(0), x_1, lean_box(0), x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_apply_2(x_4, x_5, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_instOrdNat;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Widget_CodeWithInfos_mergePosMap___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_2);
x_10 = l_Lean_Widget_TaggedText_mapM(lean_box(0), lean_box(0), lean_box(0), x_1, x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_mergePosMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Widget_CodeWithInfos_mergePosMap___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_CodeWithInfos_pretty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Widget_TaggedText_stripTags___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_SubexprInfo_withDiffTag___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Widget_SubexprInfo_withDiffTag(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_dec(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_RBNode_find___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(x_1, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_3);
lean_dec(x_6);
x_9 = l_Lean_Widget_tagCodeInfos_go(x_2, x_1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PersistentArray_empty(lean_box(0));
lean_inc(x_2);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Lean_Widget_tagCodeInfos_go(x_2, x_1, x_4);
lean_ctor_set_tag(x_3, 2);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_1);
x_17 = l_Lean_RBNode_find___at___Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = l_Lean_Widget_tagCodeInfos_go(x_2, x_1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_PersistentArray_empty(lean_box(0));
lean_inc(x_2);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Lean_Widget_tagCodeInfos_go(x_2, x_1, x_4);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Widget_tagCodeInfos_go___lam__0), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = l_Lean_Widget_TaggedText_rewrite___redArg(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_tagCodeInfos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Widget_tagCodeInfos_go(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Widget_ppExprTagged(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
x_15 = l_Lean_pp_raw;
x_16 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_PrettyPrinter_ppExprWithInfos(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_st_ref_get(x_6, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_st_ref_get(x_4, x_26);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_st_ref_get(x_6, x_30);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_unsigned_to_nat(120u);
x_36 = l_Lean_Widget_TaggedText_prettyTagged(x_21, x_34, x_35);
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_5, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 7);
lean_inc(x_40);
lean_dec(x_5);
x_41 = lean_ctor_get(x_33, 2);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_mk_string_unchecked("", 0, 0);
x_43 = l_Array_empty(lean_box(0));
lean_ctor_set(x_27, 1, x_43);
lean_ctor_set(x_27, 0, x_42);
x_44 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_27);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_14);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
x_45 = lean_box(0);
lean_ctor_set(x_23, 1, x_45);
lean_ctor_set(x_23, 0, x_44);
x_46 = l_Lean_Widget_tagCodeInfos_go(x_23, x_22, x_36);
lean_ctor_set(x_31, 0, x_46);
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_unsigned_to_nat(120u);
x_51 = l_Lean_Widget_TaggedText_prettyTagged(x_21, x_49, x_50);
x_52 = lean_ctor_get(x_25, 0);
lean_inc(x_52);
lean_dec(x_25);
x_53 = lean_ctor_get(x_29, 0);
lean_inc(x_53);
lean_dec(x_29);
x_54 = lean_ctor_get(x_5, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_5, 7);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_ctor_get(x_47, 2);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_mk_string_unchecked("", 0, 0);
x_58 = l_Array_empty(lean_box(0));
lean_ctor_set(x_27, 1, x_58);
lean_ctor_set(x_27, 0, x_57);
x_59 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_14);
lean_ctor_set(x_59, 4, x_54);
lean_ctor_set(x_59, 5, x_55);
lean_ctor_set(x_59, 6, x_56);
x_60 = lean_box(0);
lean_ctor_set(x_23, 1, x_60);
lean_ctor_set(x_23, 0, x_59);
x_61 = l_Lean_Widget_tagCodeInfos_go(x_23, x_22, x_51);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_48);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_63 = lean_ctor_get(x_27, 0);
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_27);
x_65 = lean_st_ref_get(x_6, x_64);
lean_dec(x_6);
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
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_unsigned_to_nat(120u);
x_71 = l_Lean_Widget_TaggedText_prettyTagged(x_21, x_69, x_70);
x_72 = lean_ctor_get(x_25, 0);
lean_inc(x_72);
lean_dec(x_25);
x_73 = lean_ctor_get(x_63, 0);
lean_inc(x_73);
lean_dec(x_63);
x_74 = lean_ctor_get(x_5, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_5, 7);
lean_inc(x_75);
lean_dec(x_5);
x_76 = lean_ctor_get(x_66, 2);
lean_inc(x_76);
lean_dec(x_66);
x_77 = lean_mk_string_unchecked("", 0, 0);
x_78 = l_Array_empty(lean_box(0));
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_73);
lean_ctor_set(x_80, 3, x_14);
lean_ctor_set(x_80, 4, x_74);
lean_ctor_set(x_80, 5, x_75);
lean_ctor_set(x_80, 6, x_76);
x_81 = lean_box(0);
lean_ctor_set(x_23, 1, x_81);
lean_ctor_set(x_23, 0, x_80);
x_82 = l_Lean_Widget_tagCodeInfos_go(x_23, x_22, x_71);
if (lean_is_scalar(x_68)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_68;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_67);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_84 = lean_ctor_get(x_23, 0);
x_85 = lean_ctor_get(x_23, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_23);
x_86 = lean_st_ref_get(x_4, x_85);
lean_dec(x_4);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_st_ref_get(x_6, x_88);
lean_dec(x_6);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_unsigned_to_nat(120u);
x_96 = l_Lean_Widget_TaggedText_prettyTagged(x_21, x_94, x_95);
x_97 = lean_ctor_get(x_84, 0);
lean_inc(x_97);
lean_dec(x_84);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_ctor_get(x_5, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_5, 7);
lean_inc(x_100);
lean_dec(x_5);
x_101 = lean_ctor_get(x_91, 2);
lean_inc(x_101);
lean_dec(x_91);
x_102 = lean_mk_string_unchecked("", 0, 0);
x_103 = l_Array_empty(lean_box(0));
if (lean_is_scalar(x_89)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_89;
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_98);
lean_ctor_set(x_105, 3, x_14);
lean_ctor_set(x_105, 4, x_99);
lean_ctor_set(x_105, 5, x_100);
lean_ctor_set(x_105, 6, x_101);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_Widget_tagCodeInfos_go(x_107, x_22, x_96);
if (lean_is_scalar(x_93)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_93;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_92);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_18);
if (x_110 == 0)
{
return x_18;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_18, 0);
x_112 = lean_ctor_get(x_18, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_18);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_114 = l_Lean_getPPInstantiateMVars(x_14);
lean_dec(x_14);
if (x_114 == 0)
{
lean_dec(x_4);
x_8 = x_1;
x_9 = x_7;
goto block_13;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_4, x_7);
lean_dec(x_4);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_8 = x_116;
x_9 = x_117;
goto block_13;
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_expr_dbg_to_string(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_TaggedText(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Widget_InteractiveCode(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_TaggedText(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Widget_instToJsonDiffTag = _init_l_Lean_Widget_instToJsonDiffTag();
lean_mark_persistent(l_Lean_Widget_instToJsonDiffTag);
l_Lean_Widget_instFromJsonDiffTag = _init_l_Lean_Widget_instFromJsonDiffTag();
lean_mark_persistent(l_Lean_Widget_instFromJsonDiffTag);
l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_549_ = _init_l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_549_();
lean_mark_persistent(l_Lean_Widget_instFromJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_549_);
l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_605_ = _init_l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_605_();
lean_mark_persistent(l_Lean_Widget_instToJsonRpcEncodablePacket____x40_Lean_Widget_InteractiveCode___hyg_605_);
l_Lean_Widget_instRpcEncodableSubexprInfo = _init_l_Lean_Widget_instRpcEncodableSubexprInfo();
lean_mark_persistent(l_Lean_Widget_instRpcEncodableSubexprInfo);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
