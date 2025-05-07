// Lean compiler output
// Module: Lean.Data.JsonRpc
// Imports: Init.System.IO Lean.Data.RBTree Lean.Data.Json
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1480____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequestID;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse___redArg____x40_Lean_Data_JsonRpc___hyg_1307____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object*, lean_object*);
extern lean_object* l_Lean_instFromJsonString;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_974____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instLTRequestID;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp;
extern lean_object* l_Lean_Json_instToJsonStructured;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError___redArg____x40_Lean_Data_JsonRpc___hyg_1480_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessage;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification___redArg____x40_Lean_Data_JsonRpc___hyg_1149____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1149____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse___redArg____x40_Lean_Data_JsonRpc___hyg_1307_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage;
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification___redArg____x40_Lean_Data_JsonRpc___hyg_1149_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_instFromJsonStructured___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed(lean_object*, lean_object*);
uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError___redArg____x40_Lean_Data_JsonRpc___hyg_1480____boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_23_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1307____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1149_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_974_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest___redArg____x40_Lean_Data_JsonRpc___hyg_974____boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest___redArg____x40_Lean_Data_JsonRpc___hyg_974_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1307_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1480_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID;
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_23_(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_string_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_string_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(2);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(2);
x_16 = lean_unbox(x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l_Lean_JsonNumber_lt(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_JsonNumber_lt(x_18, x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(2);
x_24 = lean_unbox(x_23);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
default: 
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
return x_28;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_2);
x_31 = lean_box(2);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instOrdRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_3);
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_JsonNumber_toString(x_6);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_mk_string_unchecked("null", 4, 4);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToStringRequestID___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t x_1) {
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
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(10u);
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(11u);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_JsonRpc_ErrorCode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_JsonRpc_ErrorCode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_JsonRpc_ErrorCode_toCtorIdx(x_1);
x_4 = l_Lean_JsonRpc_ErrorCode_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(32700u);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_neg(x_10);
lean_dec(x_10);
x_12 = lean_int_dec_eq(x_7, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(32600u);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_neg(x_14);
lean_dec(x_14);
x_16 = lean_int_dec_eq(x_7, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(32601u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = lean_int_dec_eq(x_7, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(32602u);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_int_dec_eq(x_7, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_unsigned_to_nat(32603u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_neg(x_26);
lean_dec(x_26);
x_28 = lean_int_dec_eq(x_7, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(32002u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_int_neg(x_30);
lean_dec(x_30);
x_32 = lean_int_dec_eq(x_7, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_unsigned_to_nat(32001u);
x_34 = lean_nat_to_int(x_33);
x_35 = lean_int_neg(x_34);
lean_dec(x_34);
x_36 = lean_int_dec_eq(x_7, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_unsigned_to_nat(32801u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_int_neg(x_38);
lean_dec(x_38);
x_40 = lean_int_dec_eq(x_7, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_unsigned_to_nat(32800u);
x_42 = lean_nat_to_int(x_41);
x_43 = lean_int_neg(x_42);
lean_dec(x_42);
x_44 = lean_int_dec_eq(x_7, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_unsigned_to_nat(32900u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_neg(x_46);
lean_dec(x_46);
x_48 = lean_int_dec_eq(x_7, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_unsigned_to_nat(32901u);
x_50 = lean_nat_to_int(x_49);
x_51 = lean_int_neg(x_50);
lean_dec(x_50);
x_52 = lean_int_dec_eq(x_7, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_unsigned_to_nat(32902u);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_int_neg(x_54);
lean_dec(x_54);
x_56 = lean_int_dec_eq(x_7, x_55);
lean_dec(x_55);
lean_dec(x_7);
if (x_56 == 0)
{
lean_dec(x_8);
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_eq(x_8, x_57);
lean_dec(x_8);
if (x_58 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_59; 
x_59 = lean_box(11);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_59);
return x_1;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_7);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_8, x_60);
lean_dec(x_8);
if (x_61 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_62; 
x_62 = lean_box(10);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_62);
return x_1;
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_7);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_eq(x_8, x_63);
lean_dec(x_8);
if (x_64 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_65; 
x_65 = lean_box(9);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_65);
return x_1;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_7);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_8, x_66);
lean_dec(x_8);
if (x_67 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_68; 
x_68 = lean_box(8);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_68);
return x_1;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_7);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_8, x_69);
lean_dec(x_8);
if (x_70 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_71; 
x_71 = lean_box(7);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_71);
return x_1;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_7);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_8, x_72);
lean_dec(x_8);
if (x_73 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_74; 
x_74 = lean_box(6);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_74);
return x_1;
}
}
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_7);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_eq(x_8, x_75);
lean_dec(x_8);
if (x_76 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_77; 
x_77 = lean_box(5);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_77);
return x_1;
}
}
}
else
{
lean_object* x_78; uint8_t x_79; 
lean_dec(x_7);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_8, x_78);
lean_dec(x_8);
if (x_79 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_80; 
x_80 = lean_box(4);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_80);
return x_1;
}
}
}
else
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_7);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_nat_dec_eq(x_8, x_81);
lean_dec(x_8);
if (x_82 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_83; 
x_83 = lean_box(3);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_83);
return x_1;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_7);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_8, x_84);
lean_dec(x_8);
if (x_85 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_86; 
x_86 = lean_box(2);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_86);
return x_1;
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_7);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_eq(x_8, x_87);
lean_dec(x_8);
if (x_88 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_89; 
x_89 = lean_box(1);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_89);
return x_1;
}
}
}
else
{
lean_object* x_90; uint8_t x_91; 
lean_dec(x_7);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_nat_dec_eq(x_8, x_90);
lean_dec(x_8);
if (x_91 == 0)
{
lean_free_object(x_1);
goto block_4;
}
else
{
lean_object* x_92; 
x_92 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_92);
return x_1;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
lean_dec(x_1);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unsigned_to_nat(32700u);
x_97 = lean_nat_to_int(x_96);
x_98 = lean_int_neg(x_97);
lean_dec(x_97);
x_99 = lean_int_dec_eq(x_94, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_unsigned_to_nat(32600u);
x_101 = lean_nat_to_int(x_100);
x_102 = lean_int_neg(x_101);
lean_dec(x_101);
x_103 = lean_int_dec_eq(x_94, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_unsigned_to_nat(32601u);
x_105 = lean_nat_to_int(x_104);
x_106 = lean_int_neg(x_105);
lean_dec(x_105);
x_107 = lean_int_dec_eq(x_94, x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_unsigned_to_nat(32602u);
x_109 = lean_nat_to_int(x_108);
x_110 = lean_int_neg(x_109);
lean_dec(x_109);
x_111 = lean_int_dec_eq(x_94, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_unsigned_to_nat(32603u);
x_113 = lean_nat_to_int(x_112);
x_114 = lean_int_neg(x_113);
lean_dec(x_113);
x_115 = lean_int_dec_eq(x_94, x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_unsigned_to_nat(32002u);
x_117 = lean_nat_to_int(x_116);
x_118 = lean_int_neg(x_117);
lean_dec(x_117);
x_119 = lean_int_dec_eq(x_94, x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_unsigned_to_nat(32001u);
x_121 = lean_nat_to_int(x_120);
x_122 = lean_int_neg(x_121);
lean_dec(x_121);
x_123 = lean_int_dec_eq(x_94, x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_unsigned_to_nat(32801u);
x_125 = lean_nat_to_int(x_124);
x_126 = lean_int_neg(x_125);
lean_dec(x_125);
x_127 = lean_int_dec_eq(x_94, x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_unsigned_to_nat(32800u);
x_129 = lean_nat_to_int(x_128);
x_130 = lean_int_neg(x_129);
lean_dec(x_129);
x_131 = lean_int_dec_eq(x_94, x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_unsigned_to_nat(32900u);
x_133 = lean_nat_to_int(x_132);
x_134 = lean_int_neg(x_133);
lean_dec(x_133);
x_135 = lean_int_dec_eq(x_94, x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_unsigned_to_nat(32901u);
x_137 = lean_nat_to_int(x_136);
x_138 = lean_int_neg(x_137);
lean_dec(x_137);
x_139 = lean_int_dec_eq(x_94, x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = lean_unsigned_to_nat(32902u);
x_141 = lean_nat_to_int(x_140);
x_142 = lean_int_neg(x_141);
lean_dec(x_141);
x_143 = lean_int_dec_eq(x_94, x_142);
lean_dec(x_142);
lean_dec(x_94);
if (x_143 == 0)
{
lean_dec(x_95);
goto block_4;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_nat_dec_eq(x_95, x_144);
lean_dec(x_95);
if (x_145 == 0)
{
goto block_4;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_box(11);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; uint8_t x_149; 
lean_dec(x_94);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_nat_dec_eq(x_95, x_148);
lean_dec(x_95);
if (x_149 == 0)
{
goto block_4;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_box(10);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_94);
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_nat_dec_eq(x_95, x_152);
lean_dec(x_95);
if (x_153 == 0)
{
goto block_4;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_box(9);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; uint8_t x_157; 
lean_dec(x_94);
x_156 = lean_unsigned_to_nat(0u);
x_157 = lean_nat_dec_eq(x_95, x_156);
lean_dec(x_95);
if (x_157 == 0)
{
goto block_4;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_box(8);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; uint8_t x_161; 
lean_dec(x_94);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_nat_dec_eq(x_95, x_160);
lean_dec(x_95);
if (x_161 == 0)
{
goto block_4;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_box(7);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; uint8_t x_165; 
lean_dec(x_94);
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_nat_dec_eq(x_95, x_164);
lean_dec(x_95);
if (x_165 == 0)
{
goto block_4;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_box(6);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
}
else
{
lean_object* x_168; uint8_t x_169; 
lean_dec(x_94);
x_168 = lean_unsigned_to_nat(0u);
x_169 = lean_nat_dec_eq(x_95, x_168);
lean_dec(x_95);
if (x_169 == 0)
{
goto block_4;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_box(5);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; uint8_t x_173; 
lean_dec(x_94);
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_nat_dec_eq(x_95, x_172);
lean_dec(x_95);
if (x_173 == 0)
{
goto block_4;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_box(4);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; uint8_t x_177; 
lean_dec(x_94);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_nat_dec_eq(x_95, x_176);
lean_dec(x_95);
if (x_177 == 0)
{
goto block_4;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_box(3);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; uint8_t x_181; 
lean_dec(x_94);
x_180 = lean_unsigned_to_nat(0u);
x_181 = lean_nat_dec_eq(x_95, x_180);
lean_dec(x_95);
if (x_181 == 0)
{
goto block_4;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_box(2);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
}
else
{
lean_object* x_184; uint8_t x_185; 
lean_dec(x_94);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_nat_dec_eq(x_95, x_184);
lean_dec(x_95);
if (x_185 == 0)
{
goto block_4;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_box(1);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; uint8_t x_189; 
lean_dec(x_94);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_eq(x_95, x_188);
lean_dec(x_95);
if (x_189 == 0)
{
goto block_4;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_box(0);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
}
}
else
{
lean_dec(x_1);
goto block_4;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("expected error code", 19, 19);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(32700u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_int_neg(x_3);
lean_dec(x_3);
x_5 = l_Lean_JsonNumber_fromInt(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(32600u);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_int_neg(x_8);
lean_dec(x_8);
x_10 = l_Lean_JsonNumber_fromInt(x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(32601u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_neg(x_13);
lean_dec(x_13);
x_15 = l_Lean_JsonNumber_fromInt(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(32602u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = l_Lean_JsonNumber_fromInt(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_unsigned_to_nat(32603u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_neg(x_23);
lean_dec(x_23);
x_25 = l_Lean_JsonNumber_fromInt(x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_unsigned_to_nat(32002u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_neg(x_28);
lean_dec(x_28);
x_30 = l_Lean_JsonNumber_fromInt(x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_unsigned_to_nat(32001u);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_int_neg(x_33);
lean_dec(x_33);
x_35 = l_Lean_JsonNumber_fromInt(x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
case 7:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_unsigned_to_nat(32801u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_int_neg(x_38);
lean_dec(x_38);
x_40 = l_Lean_JsonNumber_fromInt(x_39);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
case 8:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_unsigned_to_nat(32800u);
x_43 = lean_nat_to_int(x_42);
x_44 = lean_int_neg(x_43);
lean_dec(x_43);
x_45 = l_Lean_JsonNumber_fromInt(x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
case 9:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_unsigned_to_nat(32900u);
x_48 = lean_nat_to_int(x_47);
x_49 = lean_int_neg(x_48);
lean_dec(x_48);
x_50 = l_Lean_JsonNumber_fromInt(x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
case 10:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_unsigned_to_nat(32901u);
x_53 = lean_nat_to_int(x_52);
x_54 = lean_int_neg(x_53);
lean_dec(x_53);
x_55 = l_Lean_JsonNumber_fromInt(x_54);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_unsigned_to_nat(32902u);
x_58 = lean_nat_to_int(x_57);
x_59 = lean_int_neg(x_58);
lean_dec(x_58);
x_60 = l_Lean_JsonNumber_fromInt(x_59);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedMessage() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedRequest___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest___redArg____x40_Lean_Data_JsonRpc___hyg_974_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_apply_2(x_1, x_6, x_9);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_974_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest___redArg____x40_Lean_Data_JsonRpc___hyg_974_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest___redArg____x40_Lean_Data_JsonRpc___hyg_974____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest___redArg____x40_Lean_Data_JsonRpc___hyg_974_(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_974____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_974_(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_974____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_974____boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedNotification___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification___redArg____x40_Lean_Data_JsonRpc___hyg_1149_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_string_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_apply_2(x_1, x_5, x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1149_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification___redArg____x40_Lean_Data_JsonRpc___hyg_1149_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification___redArg____x40_Lean_Data_JsonRpc___hyg_1149____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification___redArg____x40_Lean_Data_JsonRpc___hyg_1149_(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1149____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1149_(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1149____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1149____boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedResponse___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse___redArg____x40_Lean_Data_JsonRpc___hyg_1307_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_apply_2(x_1, x_5, x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1307_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse___redArg____x40_Lean_Data_JsonRpc___hyg_1307_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse___redArg____x40_Lean_Data_JsonRpc___hyg_1307____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse___redArg____x40_Lean_Data_JsonRpc___hyg_1307_(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1307____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1307_(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1307____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1307____boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError___redArg____x40_Lean_Data_JsonRpc___hyg_1480_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(x_5, x_9);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_string_dec_eq(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159_(lean_box(0), x_1, x_7, x_11);
return x_15;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1480_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError___redArg____x40_Lean_Data_JsonRpc___hyg_1480_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError___redArg____x40_Lean_Data_JsonRpc___hyg_1480____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError___redArg____x40_Lean_Data_JsonRpc___hyg_1480_(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1480____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1480_(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1480____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1480____boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_apply_1(x_1, x_13);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_10);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
lean_inc(x_4);
lean_inc(x_2);
x_6 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeStringRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeStringRequestID___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeJsonNumberRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_string_dec_lt(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_JsonNumber_lt(x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonRpc_instDecidableLtRequestID(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_ctor_set_tag(x_1, 1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
case 3:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_ctor_set_tag(x_1, 0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("a request id needs to be a number or a string", 45, 45);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 3);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_ctor_set_tag(x_1, 2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
default: 
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonRequestID___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_5 = lean_mk_string_unchecked("2.0", 3, 3);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_12)) {
case 0:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_ctor_set_tag(x_12, 3);
x_16 = x_12;
goto block_27;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_16 = x_30;
goto block_27;
}
}
case 1:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
lean_ctor_set_tag(x_12, 2);
x_16 = x_12;
goto block_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_16 = x_33;
goto block_27;
}
}
default: 
{
lean_object* x_34; 
x_34 = lean_box(0);
x_16 = x_34;
goto block_27;
}
}
block_27:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("method", 6, 6);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("params", 6, 6);
x_25 = l_Lean_Json_opt___redArg(x_1, x_24, x_14);
x_26 = l_List_appendTR(lean_box(0), x_23, x_25);
x_8 = x_26;
goto block_11;
}
}
case 1:
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
x_38 = lean_mk_string_unchecked("method", 6, 6);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_38);
x_40 = lean_mk_string_unchecked("params", 6, 6);
x_41 = l_Lean_Json_opt___redArg(x_1, x_40, x_37);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_41);
x_8 = x_42;
goto block_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_45 = lean_mk_string_unchecked("method", 6, 6);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("params", 6, 6);
x_49 = l_Lean_Json_opt___redArg(x_1, x_48, x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_8 = x_50;
goto block_11;
}
}
case 2:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_53 = x_3;
} else {
 lean_dec_ref(x_3);
 x_53 = lean_box(0);
}
x_54 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_51)) {
case 0:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
lean_ctor_set_tag(x_51, 3);
x_55 = x_51;
goto block_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
lean_dec(x_51);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_55 = x_65;
goto block_62;
}
}
case 1:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_51);
if (x_66 == 0)
{
lean_ctor_set_tag(x_51, 2);
x_55 = x_51;
goto block_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_55 = x_68;
goto block_62;
}
}
default: 
{
lean_object* x_69; 
x_69 = lean_box(0);
x_55 = x_69;
goto block_62;
}
}
block_62:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
 lean_ctor_set_tag(x_56, 0);
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("result", 6, 6);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_8 = x_61;
goto block_11;
}
}
default: 
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_93; lean_object* x_94; 
lean_dec(x_1);
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_72 = lean_ctor_get(x_3, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 2);
lean_inc(x_73);
lean_dec(x_3);
x_93 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_70)) {
case 0:
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_70);
if (x_159 == 0)
{
lean_ctor_set_tag(x_70, 3);
x_94 = x_70;
goto block_158;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_70, 0);
lean_inc(x_160);
lean_dec(x_70);
x_161 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_94 = x_161;
goto block_158;
}
}
case 1:
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_70);
if (x_162 == 0)
{
lean_ctor_set_tag(x_70, 2);
x_94 = x_70;
goto block_158;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_70, 0);
lean_inc(x_163);
lean_dec(x_70);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_94 = x_164;
goto block_158;
}
}
default: 
{
lean_object* x_165; 
x_165 = lean_box(0);
x_94 = x_165;
goto block_158;
}
}
block_92:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("message", 7, 7);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_72);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("data", 4, 4);
x_86 = l_Lean_Json_opt___redArg(x_2, x_85, x_73);
x_87 = l_List_appendTR(lean_box(0), x_84, x_86);
x_88 = l_Lean_Json_mkObj(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_75);
lean_ctor_set(x_91, 1, x_90);
x_8 = x_91;
goto block_11;
}
block_158:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("error", 5, 5);
x_97 = lean_mk_string_unchecked("code", 4, 4);
switch (x_71) {
case 0:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_unsigned_to_nat(32700u);
x_99 = lean_nat_to_int(x_98);
x_100 = lean_int_neg(x_99);
lean_dec(x_99);
x_101 = l_Lean_JsonNumber_fromInt(x_100);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_102;
goto block_92;
}
case 1:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_unsigned_to_nat(32600u);
x_104 = lean_nat_to_int(x_103);
x_105 = lean_int_neg(x_104);
lean_dec(x_104);
x_106 = l_Lean_JsonNumber_fromInt(x_105);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_107;
goto block_92;
}
case 2:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_unsigned_to_nat(32601u);
x_109 = lean_nat_to_int(x_108);
x_110 = lean_int_neg(x_109);
lean_dec(x_109);
x_111 = l_Lean_JsonNumber_fromInt(x_110);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_112;
goto block_92;
}
case 3:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_unsigned_to_nat(32602u);
x_114 = lean_nat_to_int(x_113);
x_115 = lean_int_neg(x_114);
lean_dec(x_114);
x_116 = l_Lean_JsonNumber_fromInt(x_115);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_117;
goto block_92;
}
case 4:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_unsigned_to_nat(32603u);
x_119 = lean_nat_to_int(x_118);
x_120 = lean_int_neg(x_119);
lean_dec(x_119);
x_121 = l_Lean_JsonNumber_fromInt(x_120);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_122;
goto block_92;
}
case 5:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_unsigned_to_nat(32002u);
x_124 = lean_nat_to_int(x_123);
x_125 = lean_int_neg(x_124);
lean_dec(x_124);
x_126 = l_Lean_JsonNumber_fromInt(x_125);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_127;
goto block_92;
}
case 6:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_unsigned_to_nat(32001u);
x_129 = lean_nat_to_int(x_128);
x_130 = lean_int_neg(x_129);
lean_dec(x_129);
x_131 = l_Lean_JsonNumber_fromInt(x_130);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_132;
goto block_92;
}
case 7:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_unsigned_to_nat(32801u);
x_134 = lean_nat_to_int(x_133);
x_135 = lean_int_neg(x_134);
lean_dec(x_134);
x_136 = l_Lean_JsonNumber_fromInt(x_135);
x_137 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_137;
goto block_92;
}
case 8:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_unsigned_to_nat(32800u);
x_139 = lean_nat_to_int(x_138);
x_140 = lean_int_neg(x_139);
lean_dec(x_139);
x_141 = l_Lean_JsonNumber_fromInt(x_140);
x_142 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_142;
goto block_92;
}
case 9:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_unsigned_to_nat(32900u);
x_144 = lean_nat_to_int(x_143);
x_145 = lean_int_neg(x_144);
lean_dec(x_144);
x_146 = l_Lean_JsonNumber_fromInt(x_145);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_147;
goto block_92;
}
case 10:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_unsigned_to_nat(32901u);
x_149 = lean_nat_to_int(x_148);
x_150 = lean_int_neg(x_149);
lean_dec(x_149);
x_151 = l_Lean_JsonNumber_fromInt(x_150);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_152;
goto block_92;
}
default: 
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_unsigned_to_nat(32902u);
x_154 = lean_nat_to_int(x_153);
x_155 = lean_int_neg(x_154);
lean_dec(x_154);
x_156 = l_Lean_JsonNumber_fromInt(x_155);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_74 = x_97;
x_75 = x_95;
x_76 = x_96;
x_77 = x_157;
goto block_92;
}
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_instToJsonStructured;
x_2 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_2, 0, lean_box(0));
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonMessage___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; 
x_21 = lean_mk_string_unchecked("jsonrpc", 7, 7);
lean_inc(x_5);
x_22 = l_Lean_Json_getObjVal_x3f(x_5, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 3)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("2.0", 3, 3);
x_29 = lean_string_dec_eq(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_8;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_mk_string_unchecked("id", 2, 2);
lean_inc(x_5);
x_31 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_1, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
goto block_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_31, 0);
lean_inc(x_83);
x_84 = lean_mk_string_unchecked("method", 6, 6);
lean_inc(x_3);
lean_inc(x_5);
x_85 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_3, x_84);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_85);
lean_dec(x_83);
goto block_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_92; lean_object* x_93; 
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_92 = lean_mk_string_unchecked("params", 6, 6);
x_93 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_4, x_92);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_dec(x_93);
x_94 = lean_box(0);
x_88 = x_94;
goto block_91;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
x_88 = x_93;
goto block_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_88 = x_97;
goto block_91;
}
}
block_91:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_88);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
block_63:
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_mk_string_unchecked("error", 5, 5);
x_37 = l_Lean_Json_getObjVal_x3f(x_5, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_mk_string_unchecked("code", 4, 4);
lean_inc(x_41);
x_43 = l_Lean_Json_getObjValAs_x3f___redArg(x_41, x_2, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_mk_string_unchecked("message", 7, 7);
lean_inc(x_41);
x_49 = l_Lean_Json_getObjValAs_x3f___redArg(x_41, x_3, x_48);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_35);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_mk_string_unchecked("data", 4, 4);
x_55 = l_Lean_Json_getObjVal_x3f(x_41, x_54);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_55);
x_56 = lean_box(0);
x_57 = lean_unbox(x_47);
lean_dec(x_47);
x_9 = x_57;
x_10 = x_35;
x_11 = x_53;
x_12 = x_56;
goto block_15;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_unbox(x_47);
lean_dec(x_47);
x_9 = x_59;
x_10 = x_35;
x_11 = x_53;
x_12 = x_55;
goto block_15;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_unbox(x_47);
lean_dec(x_47);
x_9 = x_62;
x_10 = x_35;
x_11 = x_53;
x_12 = x_61;
goto block_15;
}
}
}
}
}
}
}
block_82:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_mk_string_unchecked("method", 6, 6);
lean_inc(x_3);
lean_inc(x_5);
x_65 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_3, x_64);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_65);
lean_dec(x_4);
if (lean_obj_tag(x_31) == 0)
{
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_31, 0);
lean_inc(x_66);
x_67 = lean_mk_string_unchecked("result", 6, 6);
lean_inc(x_5);
x_68 = l_Lean_Json_getObjVal_x3f(x_5, x_67);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_dec(x_68);
lean_dec(x_66);
goto block_63;
}
else
{
uint8_t x_69; 
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec(x_65);
x_76 = lean_mk_string_unchecked("params", 6, 6);
x_77 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_4, x_76);
lean_dec(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
lean_dec(x_77);
x_78 = lean_box(0);
x_16 = x_75;
x_17 = x_78;
goto block_20;
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
x_16 = x_75;
x_17 = x_77;
goto block_20;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_16 = x_75;
x_17 = x_81;
goto block_20;
}
}
}
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_8;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("only version 2.0 of JSON RPC is supported", 41, 41);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0), 1, 0);
x_2 = l_Lean_instFromJsonString;
x_3 = lean_alloc_closure((void*)(l_Lean_Json_instFromJsonStructured___lam__0), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; 
x_22 = lean_mk_string_unchecked("jsonrpc", 7, 7);
lean_inc(x_2);
x_23 = l_Lean_Json_getObjVal_x3f(x_2, x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
if (lean_obj_tag(x_27) == 3)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_mk_string_unchecked("2.0", 3, 3);
x_31 = lean_string_dec_eq(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0), 1, 0);
x_33 = l_Lean_instFromJsonString;
x_34 = lean_alloc_closure((void*)(l_Lean_Json_instFromJsonStructured___lam__0), 1, 0);
x_35 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0), 1, 0);
x_36 = lean_mk_string_unchecked("id", 2, 2);
lean_inc(x_2);
x_37 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_32, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
goto block_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_mk_string_unchecked("method", 6, 6);
lean_inc(x_2);
x_73 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_33, x_72);
lean_dec(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_73);
goto block_71;
}
else
{
lean_dec(x_73);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
goto block_5;
}
}
block_57:
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_35);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_41 = lean_mk_string_unchecked("error", 5, 5);
x_42 = l_Lean_Json_getObjVal_x3f(x_2, x_41);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_35);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_mk_string_unchecked("code", 4, 4);
lean_inc(x_46);
x_48 = l_Lean_Json_getObjValAs_x3f___redArg(x_46, x_35, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
x_52 = lean_mk_string_unchecked("message", 7, 7);
x_53 = l_Lean_Json_getObjValAs_x3f___redArg(x_46, x_33, x_52);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
lean_dec(x_53);
goto block_5;
}
}
}
}
}
block_71:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_mk_string_unchecked("method", 6, 6);
lean_inc(x_2);
x_59 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_33, x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_dec(x_59);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_1);
if (lean_obj_tag(x_37) == 0)
{
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_mk_string_unchecked("result", 6, 6);
lean_inc(x_2);
x_61 = l_Lean_Json_getObjVal_x3f(x_2, x_60);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_61);
goto block_57;
}
else
{
lean_dec(x_61);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_2);
goto block_5;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_37);
lean_dec(x_35);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_mk_string_unchecked("params", 6, 6);
x_64 = l_Lean_Json_getObjValAs_x3f___redArg(x_2, x_34, x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_64);
lean_dec(x_29);
x_65 = lean_box(0);
x_6 = x_62;
x_7 = x_65;
goto block_18;
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
if (lean_is_scalar(x_29)) {
 x_68 = lean_alloc_ctor(4, 1, 0);
} else {
 x_68 = x_29;
 lean_ctor_set_tag(x_68, 4);
}
lean_ctor_set(x_68, 0, x_67);
x_6 = x_62;
x_7 = x_68;
goto block_18;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
if (lean_is_scalar(x_29)) {
 x_70 = lean_alloc_ctor(5, 1, 0);
} else {
 x_70 = x_29;
 lean_ctor_set_tag(x_70, 5);
}
lean_ctor_set(x_70, 0, x_69);
x_6 = x_62;
x_7 = x_70;
goto block_18;
}
}
}
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_1);
goto block_21;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("not a notification", 18, 18);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
block_18:
{
lean_object* x_8; 
x_8 = lean_apply_1(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_mk_string_unchecked("only version 2.0 of JSON RPC is supported", 41, 41);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instFromJsonNotification___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 2:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_ctor_set_tag(x_3, 1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 3:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_ctor_set_tag(x_3, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_mk_string_unchecked("a request id needs to be a number or a string", 45, 45);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_6) == 2)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(32700u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
x_14 = lean_int_dec_eq(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(32600u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_int_neg(x_16);
lean_dec(x_16);
x_18 = lean_int_dec_eq(x_9, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(32601u);
x_20 = lean_nat_to_int(x_19);
x_21 = lean_int_neg(x_20);
lean_dec(x_20);
x_22 = lean_int_dec_eq(x_9, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(32602u);
x_24 = lean_nat_to_int(x_23);
x_25 = lean_int_neg(x_24);
lean_dec(x_24);
x_26 = lean_int_dec_eq(x_9, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_unsigned_to_nat(32603u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_neg(x_28);
lean_dec(x_28);
x_30 = lean_int_dec_eq(x_9, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_unsigned_to_nat(32002u);
x_32 = lean_nat_to_int(x_31);
x_33 = lean_int_neg(x_32);
lean_dec(x_32);
x_34 = lean_int_dec_eq(x_9, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_unsigned_to_nat(32001u);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_int_neg(x_36);
lean_dec(x_36);
x_38 = lean_int_dec_eq(x_9, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_unsigned_to_nat(32801u);
x_40 = lean_nat_to_int(x_39);
x_41 = lean_int_neg(x_40);
lean_dec(x_40);
x_42 = lean_int_dec_eq(x_9, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_unsigned_to_nat(32800u);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_int_neg(x_44);
lean_dec(x_44);
x_46 = lean_int_dec_eq(x_9, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_unsigned_to_nat(32900u);
x_48 = lean_nat_to_int(x_47);
x_49 = lean_int_neg(x_48);
lean_dec(x_48);
x_50 = lean_int_dec_eq(x_9, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_unsigned_to_nat(32901u);
x_52 = lean_nat_to_int(x_51);
x_53 = lean_int_neg(x_52);
lean_dec(x_52);
x_54 = lean_int_dec_eq(x_9, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_unsigned_to_nat(32902u);
x_56 = lean_nat_to_int(x_55);
x_57 = lean_int_neg(x_56);
lean_dec(x_56);
x_58 = lean_int_dec_eq(x_9, x_57);
lean_dec(x_57);
lean_dec(x_9);
if (x_58 == 0)
{
lean_dec(x_10);
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_eq(x_10, x_59);
lean_dec(x_10);
if (x_60 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_61; 
x_61 = lean_box(11);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_61);
return x_6;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_9);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_10, x_62);
lean_dec(x_10);
if (x_63 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_64; 
x_64 = lean_box(10);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_64);
return x_6;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_9);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_10, x_65);
lean_dec(x_10);
if (x_66 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_67; 
x_67 = lean_box(9);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_67);
return x_6;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_9);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_eq(x_10, x_68);
lean_dec(x_10);
if (x_69 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_70; 
x_70 = lean_box(8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_70);
return x_6;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_dec(x_9);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_eq(x_10, x_71);
lean_dec(x_10);
if (x_72 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_73; 
x_73 = lean_box(7);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_73);
return x_6;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_9);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_10, x_74);
lean_dec(x_10);
if (x_75 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_76; 
x_76 = lean_box(6);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_76);
return x_6;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_9);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_10, x_77);
lean_dec(x_10);
if (x_78 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_79; 
x_79 = lean_box(5);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_79);
return x_6;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_9);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_nat_dec_eq(x_10, x_80);
lean_dec(x_10);
if (x_81 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_82; 
x_82 = lean_box(4);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_82);
return x_6;
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_9);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_nat_dec_eq(x_10, x_83);
lean_dec(x_10);
if (x_84 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_85; 
x_85 = lean_box(3);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_85);
return x_6;
}
}
}
else
{
lean_object* x_86; uint8_t x_87; 
lean_dec(x_9);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_eq(x_10, x_86);
lean_dec(x_10);
if (x_87 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_88; 
x_88 = lean_box(2);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_88);
return x_6;
}
}
}
else
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_9);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_nat_dec_eq(x_10, x_89);
lean_dec(x_10);
if (x_90 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_91; 
x_91 = lean_box(1);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_91);
return x_6;
}
}
}
else
{
lean_object* x_92; uint8_t x_93; 
lean_dec(x_9);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_dec_eq(x_10, x_92);
lean_dec(x_10);
if (x_93 == 0)
{
lean_free_object(x_6);
goto block_5;
}
else
{
lean_object* x_94; 
x_94 = lean_box(0);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_94);
return x_6;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_6, 0);
lean_inc(x_95);
lean_dec(x_6);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unsigned_to_nat(32700u);
x_99 = lean_nat_to_int(x_98);
x_100 = lean_int_neg(x_99);
lean_dec(x_99);
x_101 = lean_int_dec_eq(x_96, x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_unsigned_to_nat(32600u);
x_103 = lean_nat_to_int(x_102);
x_104 = lean_int_neg(x_103);
lean_dec(x_103);
x_105 = lean_int_dec_eq(x_96, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_unsigned_to_nat(32601u);
x_107 = lean_nat_to_int(x_106);
x_108 = lean_int_neg(x_107);
lean_dec(x_107);
x_109 = lean_int_dec_eq(x_96, x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_unsigned_to_nat(32602u);
x_111 = lean_nat_to_int(x_110);
x_112 = lean_int_neg(x_111);
lean_dec(x_111);
x_113 = lean_int_dec_eq(x_96, x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_unsigned_to_nat(32603u);
x_115 = lean_nat_to_int(x_114);
x_116 = lean_int_neg(x_115);
lean_dec(x_115);
x_117 = lean_int_dec_eq(x_96, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_unsigned_to_nat(32002u);
x_119 = lean_nat_to_int(x_118);
x_120 = lean_int_neg(x_119);
lean_dec(x_119);
x_121 = lean_int_dec_eq(x_96, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_unsigned_to_nat(32001u);
x_123 = lean_nat_to_int(x_122);
x_124 = lean_int_neg(x_123);
lean_dec(x_123);
x_125 = lean_int_dec_eq(x_96, x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_unsigned_to_nat(32801u);
x_127 = lean_nat_to_int(x_126);
x_128 = lean_int_neg(x_127);
lean_dec(x_127);
x_129 = lean_int_dec_eq(x_96, x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_unsigned_to_nat(32800u);
x_131 = lean_nat_to_int(x_130);
x_132 = lean_int_neg(x_131);
lean_dec(x_131);
x_133 = lean_int_dec_eq(x_96, x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_unsigned_to_nat(32900u);
x_135 = lean_nat_to_int(x_134);
x_136 = lean_int_neg(x_135);
lean_dec(x_135);
x_137 = lean_int_dec_eq(x_96, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_unsigned_to_nat(32901u);
x_139 = lean_nat_to_int(x_138);
x_140 = lean_int_neg(x_139);
lean_dec(x_139);
x_141 = lean_int_dec_eq(x_96, x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_unsigned_to_nat(32902u);
x_143 = lean_nat_to_int(x_142);
x_144 = lean_int_neg(x_143);
lean_dec(x_143);
x_145 = lean_int_dec_eq(x_96, x_144);
lean_dec(x_144);
lean_dec(x_96);
if (x_145 == 0)
{
lean_dec(x_97);
goto block_5;
}
else
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_eq(x_97, x_146);
lean_dec(x_97);
if (x_147 == 0)
{
goto block_5;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_box(11);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; uint8_t x_151; 
lean_dec(x_96);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_nat_dec_eq(x_97, x_150);
lean_dec(x_97);
if (x_151 == 0)
{
goto block_5;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_box(10);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_96);
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_nat_dec_eq(x_97, x_154);
lean_dec(x_97);
if (x_155 == 0)
{
goto block_5;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_box(9);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; uint8_t x_159; 
lean_dec(x_96);
x_158 = lean_unsigned_to_nat(0u);
x_159 = lean_nat_dec_eq(x_97, x_158);
lean_dec(x_97);
if (x_159 == 0)
{
goto block_5;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_box(8);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; 
lean_dec(x_96);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_nat_dec_eq(x_97, x_162);
lean_dec(x_97);
if (x_163 == 0)
{
goto block_5;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_box(7);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; uint8_t x_167; 
lean_dec(x_96);
x_166 = lean_unsigned_to_nat(0u);
x_167 = lean_nat_dec_eq(x_97, x_166);
lean_dec(x_97);
if (x_167 == 0)
{
goto block_5;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_box(6);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; uint8_t x_171; 
lean_dec(x_96);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_nat_dec_eq(x_97, x_170);
lean_dec(x_97);
if (x_171 == 0)
{
goto block_5;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_box(5);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_96);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_nat_dec_eq(x_97, x_174);
lean_dec(x_97);
if (x_175 == 0)
{
goto block_5;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_box(4);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; uint8_t x_179; 
lean_dec(x_96);
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_nat_dec_eq(x_97, x_178);
lean_dec(x_97);
if (x_179 == 0)
{
goto block_5;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_box(3);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
else
{
lean_object* x_182; uint8_t x_183; 
lean_dec(x_96);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_nat_dec_eq(x_97, x_182);
lean_dec(x_97);
if (x_183 == 0)
{
goto block_5;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_box(2);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
else
{
lean_object* x_186; uint8_t x_187; 
lean_dec(x_96);
x_186 = lean_unsigned_to_nat(0u);
x_187 = lean_nat_dec_eq(x_97, x_186);
lean_dec(x_97);
if (x_187 == 0)
{
goto block_5;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_box(1);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; uint8_t x_191; 
lean_dec(x_96);
x_190 = lean_unsigned_to_nat(0u);
x_191 = lean_nat_dec_eq(x_97, x_190);
lean_dec(x_97);
if (x_191 == 0)
{
goto block_5;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
}
}
}
else
{
lean_dec(x_6);
goto block_5;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("expected error code", 19, 19);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 4:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_ctor_set_tag(x_3, 0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 5:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_ctor_set_tag(x_3, 1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
x_15 = lean_unsigned_to_nat(80u);
x_16 = l_Lean_Json_pretty(x_3, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readJson(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_32; lean_object* x_33; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_32 = lean_mk_string_unchecked("jsonrpc", 7, 7);
lean_inc(x_5);
x_33 = l_Lean_Json_getObjVal_x3f(x_5, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_20 = x_34;
goto block_29;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 3)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_mk_string_unchecked("2.0", 3, 3);
x_38 = lean_string_dec_eq(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_dec(x_7);
goto block_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_mk_string_unchecked("id", 2, 2);
lean_inc(x_5);
x_40 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(x_5, x_39);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
goto block_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_40, 0);
lean_inc(x_81);
x_82 = lean_mk_string_unchecked("method", 6, 6);
lean_inc(x_5);
x_83 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_5, x_82);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_dec(x_83);
lean_dec(x_81);
goto block_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_89; lean_object* x_90; 
lean_dec(x_40);
lean_dec(x_7);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_89 = lean_mk_string_unchecked("params", 6, 6);
x_90 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__3(x_5, x_89);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec(x_90);
x_91 = lean_box(0);
x_85 = x_91;
goto block_88;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
x_85 = x_90;
goto block_88;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_85 = x_94;
goto block_88;
}
}
block_88:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
block_64:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_7);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_20 = x_41;
goto block_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_mk_string_unchecked("error", 5, 5);
lean_inc(x_5);
x_44 = l_Lean_Json_getObjVal_x3f(x_5, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_20 = x_45;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_mk_string_unchecked("code", 4, 4);
lean_inc(x_46);
x_48 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__1(x_46, x_47);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_20 = x_49;
goto block_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_mk_string_unchecked("message", 7, 7);
lean_inc(x_46);
x_52 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_46, x_51);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_20 = x_53;
goto block_29;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_5);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_mk_string_unchecked("data", 4, 4);
x_56 = l_Lean_Json_getObjVal_x3f(x_46, x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_56);
x_57 = lean_box(0);
x_58 = lean_unbox(x_50);
lean_dec(x_50);
x_8 = x_58;
x_9 = x_54;
x_10 = x_42;
x_11 = x_57;
goto block_14;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = lean_unbox(x_50);
lean_dec(x_50);
x_8 = x_60;
x_9 = x_54;
x_10 = x_42;
x_11 = x_56;
goto block_14;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox(x_50);
lean_dec(x_50);
x_8 = x_63;
x_9 = x_54;
x_10 = x_42;
x_11 = x_62;
goto block_14;
}
}
}
}
}
}
}
block_80:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_mk_string_unchecked("method", 6, 6);
lean_inc(x_5);
x_66 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_5, x_65);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_66);
if (lean_obj_tag(x_40) == 0)
{
goto block_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_40, 0);
lean_inc(x_67);
x_68 = lean_mk_string_unchecked("result", 6, 6);
lean_inc(x_5);
x_69 = l_Lean_Json_getObjVal_x3f(x_5, x_68);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_dec(x_69);
lean_dec(x_67);
goto block_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_5);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_6);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_40);
lean_dec(x_7);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_mk_string_unchecked("params", 6, 6);
x_75 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__3(x_5, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_75);
x_76 = lean_box(0);
x_15 = x_73;
x_16 = x_76;
goto block_19;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
x_15 = x_73;
x_16 = x_75;
goto block_19;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_15 = x_73;
x_16 = x_79;
goto block_19;
}
}
}
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_7);
goto block_31;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_8);
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_7;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
block_29:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_mk_string_unchecked("JSON '", 6, 6);
x_22 = l_Lean_Json_compress(x_5);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("' did not have the format of a JSON-RPC message.\n", 49, 49);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_25, x_20);
lean_dec(x_20);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
block_31:
{
lean_object* x_30; 
x_30 = lean_mk_string_unchecked("only version 2.0 of JSON RPC is supported", 41, 41);
x_20 = x_30;
goto block_29;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_4);
if (x_95 == 0)
{
return x_4;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_4, 0);
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_4);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_44; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_13 = x_7;
} else {
 lean_dec_ref(x_7);
 x_13 = lean_box(0);
}
x_44 = lean_string_dec_eq(x_11, x_3);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_45 = lean_mk_string_unchecked("Expected method '", 17, 17);
x_46 = lean_string_append(x_45, x_3);
lean_dec(x_3);
x_47 = lean_mk_string_unchecked("', got method '", 15, 15);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_string_append(x_48, x_11);
lean_dec(x_11);
x_50 = lean_mk_string_unchecked("'", 1, 1);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_8);
return x_53;
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_14 = x_54;
goto block_43;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_12, 0);
lean_inc(x_55);
lean_dec(x_12);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_ctor_set_tag(x_55, 4);
x_14 = x_55;
goto block_43;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_14 = x_58;
goto block_43;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_ctor_set_tag(x_55, 5);
x_14 = x_55;
goto block_43;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_14 = x_61;
goto block_43;
}
}
}
}
block_43:
{
lean_object* x_15; 
lean_inc(x_14);
x_15 = lean_apply_1(x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_19 = l_Lean_Json_compress(x_14);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked("' for method '", 14, 14);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_3);
lean_dec(x_3);
x_24 = lean_mk_string_unchecked("'\n", 2, 2);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_25, x_17);
lean_dec(x_17);
lean_ctor_set_tag(x_15, 18);
lean_ctor_set(x_15, 0, x_26);
if (lean_is_scalar(x_9)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_9;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_30 = l_Lean_Json_compress(x_14);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("' for method '", 14, 14);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_33, x_3);
lean_dec(x_3);
x_35 = lean_mk_string_unchecked("'\n", 2, 2);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_string_append(x_36, x_28);
lean_dec(x_28);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_9)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_9;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_14);
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
if (lean_is_scalar(x_13)) {
 x_41 = lean_alloc_ctor(0, 3, 0);
} else {
 x_41 = x_13;
}
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set(x_41, 2, x_40);
if (lean_is_scalar(x_9)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_9;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
lean_dec(x_3);
x_62 = lean_ctor_get(x_6, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_63 = x_6;
} else {
 lean_dec_ref(x_6);
 x_63 = lean_box(0);
}
x_64 = lean_mk_string_unchecked("Expected JSON-RPC request, got: '", 33, 33);
x_65 = l_Lean_Json_instToJsonStructured;
x_66 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_67 = lean_mk_string_unchecked("2.0", 3, 3);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_7, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_7, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_7, 2);
lean_inc(x_82);
lean_dec(x_7);
x_83 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_80);
if (x_96 == 0)
{
lean_ctor_set_tag(x_80, 3);
x_84 = x_80;
goto block_95;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_80, 0);
lean_inc(x_97);
lean_dec(x_80);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_84 = x_98;
goto block_95;
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_80);
if (x_99 == 0)
{
lean_ctor_set_tag(x_80, 2);
x_84 = x_80;
goto block_95;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_80, 0);
lean_inc(x_100);
lean_dec(x_80);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_84 = x_101;
goto block_95;
}
}
block_95:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked("method", 6, 6);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_85);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("params", 6, 6);
x_93 = l_Lean_Json_opt___redArg(x_65, x_92, x_82);
x_94 = l_List_appendTR(lean_box(0), x_91, x_93);
x_70 = x_94;
goto block_79;
}
}
case 1:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_7, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_7, 1);
lean_inc(x_103);
lean_dec(x_7);
x_104 = lean_mk_string_unchecked("method", 6, 6);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("params", 6, 6);
x_108 = l_Lean_Json_opt___redArg(x_65, x_107, x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_70 = x_109;
goto block_79;
}
case 2:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_7, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_7, 1);
lean_inc(x_111);
lean_dec(x_7);
x_112 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_110);
if (x_121 == 0)
{
lean_ctor_set_tag(x_110, 3);
x_113 = x_110;
goto block_120;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_110, 0);
lean_inc(x_122);
lean_dec(x_110);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_113 = x_123;
goto block_120;
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_110);
if (x_124 == 0)
{
lean_ctor_set_tag(x_110, 2);
x_113 = x_110;
goto block_120;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
lean_dec(x_110);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_113 = x_126;
goto block_120;
}
}
block_120:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked("result", 6, 6);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_118);
x_70 = x_119;
goto block_79;
}
}
default: 
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_151; lean_object* x_152; 
x_127 = lean_ctor_get(x_7, 0);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_7, 2);
lean_inc(x_130);
lean_dec(x_7);
x_131 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_131, 0, lean_box(0));
x_151 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_127);
if (x_217 == 0)
{
lean_ctor_set_tag(x_127, 3);
x_152 = x_127;
goto block_216;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_127, 0);
lean_inc(x_218);
lean_dec(x_127);
x_219 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_152 = x_219;
goto block_216;
}
}
else
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_127);
if (x_220 == 0)
{
lean_ctor_set_tag(x_127, 2);
x_152 = x_127;
goto block_216;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_127, 0);
lean_inc(x_221);
lean_dec(x_127);
x_222 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_152 = x_222;
goto block_216;
}
}
block_150:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked("message", 7, 7);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_129);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked("data", 4, 4);
x_144 = l_Lean_Json_opt___redArg(x_131, x_143, x_130);
x_145 = l_List_appendTR(lean_box(0), x_142, x_144);
x_146 = l_Lean_Json_mkObj(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_133);
lean_ctor_set(x_149, 1, x_148);
x_70 = x_149;
goto block_79;
}
block_216:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_mk_string_unchecked("error", 5, 5);
x_155 = lean_mk_string_unchecked("code", 4, 4);
switch (x_128) {
case 0:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_unsigned_to_nat(32700u);
x_157 = lean_nat_to_int(x_156);
x_158 = lean_int_neg(x_157);
lean_dec(x_157);
x_159 = l_Lean_JsonNumber_fromInt(x_158);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_160;
goto block_150;
}
case 1:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_unsigned_to_nat(32600u);
x_162 = lean_nat_to_int(x_161);
x_163 = lean_int_neg(x_162);
lean_dec(x_162);
x_164 = l_Lean_JsonNumber_fromInt(x_163);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_165;
goto block_150;
}
case 2:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_unsigned_to_nat(32601u);
x_167 = lean_nat_to_int(x_166);
x_168 = lean_int_neg(x_167);
lean_dec(x_167);
x_169 = l_Lean_JsonNumber_fromInt(x_168);
x_170 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_170;
goto block_150;
}
case 3:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_unsigned_to_nat(32602u);
x_172 = lean_nat_to_int(x_171);
x_173 = lean_int_neg(x_172);
lean_dec(x_172);
x_174 = l_Lean_JsonNumber_fromInt(x_173);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_175;
goto block_150;
}
case 4:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_unsigned_to_nat(32603u);
x_177 = lean_nat_to_int(x_176);
x_178 = lean_int_neg(x_177);
lean_dec(x_177);
x_179 = l_Lean_JsonNumber_fromInt(x_178);
x_180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_180;
goto block_150;
}
case 5:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_unsigned_to_nat(32002u);
x_182 = lean_nat_to_int(x_181);
x_183 = lean_int_neg(x_182);
lean_dec(x_182);
x_184 = l_Lean_JsonNumber_fromInt(x_183);
x_185 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_185;
goto block_150;
}
case 6:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_unsigned_to_nat(32001u);
x_187 = lean_nat_to_int(x_186);
x_188 = lean_int_neg(x_187);
lean_dec(x_187);
x_189 = l_Lean_JsonNumber_fromInt(x_188);
x_190 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_190;
goto block_150;
}
case 7:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_unsigned_to_nat(32801u);
x_192 = lean_nat_to_int(x_191);
x_193 = lean_int_neg(x_192);
lean_dec(x_192);
x_194 = l_Lean_JsonNumber_fromInt(x_193);
x_195 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_195;
goto block_150;
}
case 8:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_unsigned_to_nat(32800u);
x_197 = lean_nat_to_int(x_196);
x_198 = lean_int_neg(x_197);
lean_dec(x_197);
x_199 = l_Lean_JsonNumber_fromInt(x_198);
x_200 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_200;
goto block_150;
}
case 9:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_unsigned_to_nat(32900u);
x_202 = lean_nat_to_int(x_201);
x_203 = lean_int_neg(x_202);
lean_dec(x_202);
x_204 = l_Lean_JsonNumber_fromInt(x_203);
x_205 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_205;
goto block_150;
}
case 10:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_unsigned_to_nat(32901u);
x_207 = lean_nat_to_int(x_206);
x_208 = lean_int_neg(x_207);
lean_dec(x_207);
x_209 = l_Lean_JsonNumber_fromInt(x_208);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_210;
goto block_150;
}
default: 
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_unsigned_to_nat(32902u);
x_212 = lean_nat_to_int(x_211);
x_213 = lean_int_neg(x_212);
lean_dec(x_212);
x_214 = l_Lean_JsonNumber_fromInt(x_213);
x_215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_132 = x_154;
x_133 = x_153;
x_134 = x_155;
x_135 = x_215;
goto block_150;
}
}
}
}
}
block_79:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Json_mkObj(x_71);
x_73 = l_Lean_Json_compress(x_72);
x_74 = lean_string_append(x_64, x_73);
lean_dec(x_73);
x_75 = lean_mk_string_unchecked("'", 1, 1);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_63)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_63;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_62);
return x_78;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_4);
lean_dec(x_3);
x_223 = !lean_is_exclusive(x_6);
if (x_223 == 0)
{
return x_6;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_6, 0);
x_225 = lean_ctor_get(x_6, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_6);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
x_43 = lean_string_dec_eq(x_41, x_3);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_4);
x_44 = lean_mk_string_unchecked("Expected method '", 17, 17);
x_45 = lean_string_append(x_44, x_3);
lean_dec(x_3);
x_46 = lean_mk_string_unchecked("', got method '", 15, 15);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = lean_string_append(x_47, x_41);
lean_dec(x_41);
x_49 = lean_mk_string_unchecked("'", 1, 1);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_7, 1, x_8);
lean_ctor_set(x_7, 0, x_51);
return x_7;
}
else
{
lean_free_object(x_7);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_10 = x_52;
goto block_39;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
lean_dec(x_42);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_ctor_set_tag(x_53, 4);
x_10 = x_53;
goto block_39;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_10 = x_56;
goto block_39;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_ctor_set_tag(x_53, 5);
x_10 = x_53;
goto block_39;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_10 = x_59;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_7, 0);
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_7);
x_62 = lean_string_dec_eq(x_60, x_3);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_4);
x_63 = lean_mk_string_unchecked("Expected method '", 17, 17);
x_64 = lean_string_append(x_63, x_3);
lean_dec(x_3);
x_65 = lean_mk_string_unchecked("', got method '", 15, 15);
x_66 = lean_string_append(x_64, x_65);
lean_dec(x_65);
x_67 = lean_string_append(x_66, x_60);
lean_dec(x_60);
x_68 = lean_mk_string_unchecked("'", 1, 1);
x_69 = lean_string_append(x_67, x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_8);
return x_71;
}
else
{
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_72; 
x_72 = lean_box(0);
x_10 = x_72;
goto block_39;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
lean_dec(x_61);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(4, 1, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 4);
}
lean_ctor_set(x_76, 0, x_74);
x_10 = x_76;
goto block_39;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(5, 1, 0);
} else {
 x_79 = x_78;
 lean_ctor_set_tag(x_79, 5);
}
lean_ctor_set(x_79, 0, x_77);
x_10 = x_79;
goto block_39;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_mk_string_unchecked("Expected JSON-RPC notification, got: '", 38, 38);
x_81 = l_Lean_Json_instToJsonStructured;
x_82 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_83 = lean_mk_string_unchecked("2.0", 3, 3);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_7, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_7, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_7, 2);
lean_inc(x_98);
lean_dec(x_7);
x_99 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_96);
if (x_112 == 0)
{
lean_ctor_set_tag(x_96, 3);
x_100 = x_96;
goto block_111;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_96, 0);
lean_inc(x_113);
lean_dec(x_96);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_100 = x_114;
goto block_111;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_96);
if (x_115 == 0)
{
lean_ctor_set_tag(x_96, 2);
x_100 = x_96;
goto block_111;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_96, 0);
lean_inc(x_116);
lean_dec(x_96);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_100 = x_117;
goto block_111;
}
}
block_111:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_mk_string_unchecked("method", 6, 6);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_97);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked("params", 6, 6);
x_109 = l_Lean_Json_opt___redArg(x_81, x_108, x_98);
x_110 = l_List_appendTR(lean_box(0), x_107, x_109);
x_86 = x_110;
goto block_95;
}
}
case 1:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_7, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_7, 1);
lean_inc(x_119);
lean_dec(x_7);
x_120 = lean_mk_string_unchecked("method", 6, 6);
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_mk_string_unchecked("params", 6, 6);
x_124 = l_Lean_Json_opt___redArg(x_81, x_123, x_119);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
x_86 = x_125;
goto block_95;
}
case 2:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_7, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_7, 1);
lean_inc(x_127);
lean_dec(x_7);
x_128 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_126);
if (x_137 == 0)
{
lean_ctor_set_tag(x_126, 3);
x_129 = x_126;
goto block_136;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_126, 0);
lean_inc(x_138);
lean_dec(x_126);
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_129 = x_139;
goto block_136;
}
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_126);
if (x_140 == 0)
{
lean_ctor_set_tag(x_126, 2);
x_129 = x_126;
goto block_136;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_126, 0);
lean_inc(x_141);
lean_dec(x_126);
x_142 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_129 = x_142;
goto block_136;
}
}
block_136:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_mk_string_unchecked("result", 6, 6);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_127);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_134);
x_86 = x_135;
goto block_95;
}
}
default: 
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_167; lean_object* x_168; 
x_143 = lean_ctor_get(x_7, 0);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_145 = lean_ctor_get(x_7, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_7, 2);
lean_inc(x_146);
lean_dec(x_7);
x_147 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_147, 0, lean_box(0));
x_167 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_143);
if (x_233 == 0)
{
lean_ctor_set_tag(x_143, 3);
x_168 = x_143;
goto block_232;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_143, 0);
lean_inc(x_234);
lean_dec(x_143);
x_235 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_168 = x_235;
goto block_232;
}
}
else
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_143);
if (x_236 == 0)
{
lean_ctor_set_tag(x_143, 2);
x_168 = x_143;
goto block_232;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_143, 0);
lean_inc(x_237);
lean_dec(x_143);
x_238 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_168 = x_238;
goto block_232;
}
}
block_166:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_mk_string_unchecked("message", 7, 7);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_145);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_string_unchecked("data", 4, 4);
x_160 = l_Lean_Json_opt___redArg(x_147, x_159, x_146);
x_161 = l_List_appendTR(lean_box(0), x_158, x_160);
x_162 = l_Lean_Json_mkObj(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_148);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_156);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_149);
lean_ctor_set(x_165, 1, x_164);
x_86 = x_165;
goto block_95;
}
block_232:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_mk_string_unchecked("error", 5, 5);
x_171 = lean_mk_string_unchecked("code", 4, 4);
switch (x_144) {
case 0:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_unsigned_to_nat(32700u);
x_173 = lean_nat_to_int(x_172);
x_174 = lean_int_neg(x_173);
lean_dec(x_173);
x_175 = l_Lean_JsonNumber_fromInt(x_174);
x_176 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_176;
goto block_166;
}
case 1:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_unsigned_to_nat(32600u);
x_178 = lean_nat_to_int(x_177);
x_179 = lean_int_neg(x_178);
lean_dec(x_178);
x_180 = l_Lean_JsonNumber_fromInt(x_179);
x_181 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_181;
goto block_166;
}
case 2:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_unsigned_to_nat(32601u);
x_183 = lean_nat_to_int(x_182);
x_184 = lean_int_neg(x_183);
lean_dec(x_183);
x_185 = l_Lean_JsonNumber_fromInt(x_184);
x_186 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_186;
goto block_166;
}
case 3:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_unsigned_to_nat(32602u);
x_188 = lean_nat_to_int(x_187);
x_189 = lean_int_neg(x_188);
lean_dec(x_188);
x_190 = l_Lean_JsonNumber_fromInt(x_189);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_191;
goto block_166;
}
case 4:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_unsigned_to_nat(32603u);
x_193 = lean_nat_to_int(x_192);
x_194 = lean_int_neg(x_193);
lean_dec(x_193);
x_195 = l_Lean_JsonNumber_fromInt(x_194);
x_196 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_196;
goto block_166;
}
case 5:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_unsigned_to_nat(32002u);
x_198 = lean_nat_to_int(x_197);
x_199 = lean_int_neg(x_198);
lean_dec(x_198);
x_200 = l_Lean_JsonNumber_fromInt(x_199);
x_201 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_201;
goto block_166;
}
case 6:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_unsigned_to_nat(32001u);
x_203 = lean_nat_to_int(x_202);
x_204 = lean_int_neg(x_203);
lean_dec(x_203);
x_205 = l_Lean_JsonNumber_fromInt(x_204);
x_206 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_206;
goto block_166;
}
case 7:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_unsigned_to_nat(32801u);
x_208 = lean_nat_to_int(x_207);
x_209 = lean_int_neg(x_208);
lean_dec(x_208);
x_210 = l_Lean_JsonNumber_fromInt(x_209);
x_211 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_211;
goto block_166;
}
case 8:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_unsigned_to_nat(32800u);
x_213 = lean_nat_to_int(x_212);
x_214 = lean_int_neg(x_213);
lean_dec(x_213);
x_215 = l_Lean_JsonNumber_fromInt(x_214);
x_216 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_216;
goto block_166;
}
case 9:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_unsigned_to_nat(32900u);
x_218 = lean_nat_to_int(x_217);
x_219 = lean_int_neg(x_218);
lean_dec(x_218);
x_220 = l_Lean_JsonNumber_fromInt(x_219);
x_221 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_221;
goto block_166;
}
case 10:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_unsigned_to_nat(32901u);
x_223 = lean_nat_to_int(x_222);
x_224 = lean_int_neg(x_223);
lean_dec(x_223);
x_225 = l_Lean_JsonNumber_fromInt(x_224);
x_226 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_226;
goto block_166;
}
default: 
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_unsigned_to_nat(32902u);
x_228 = lean_nat_to_int(x_227);
x_229 = lean_int_neg(x_228);
lean_dec(x_228);
x_230 = l_Lean_JsonNumber_fromInt(x_229);
x_231 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_148 = x_170;
x_149 = x_169;
x_150 = x_171;
x_151 = x_231;
goto block_166;
}
}
}
}
}
block_95:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Json_mkObj(x_87);
x_89 = l_Lean_Json_compress(x_88);
x_90 = lean_string_append(x_80, x_89);
lean_dec(x_89);
x_91 = lean_mk_string_unchecked("'", 1, 1);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_8);
return x_94;
}
}
block_39:
{
lean_object* x_11; 
lean_inc(x_10);
x_11 = lean_apply_1(x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_15 = l_Lean_Json_compress(x_10);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("' for method '", 14, 14);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_3);
lean_dec(x_3);
x_20 = lean_mk_string_unchecked("'\n", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_13);
lean_dec(x_13);
lean_ctor_set_tag(x_11, 18);
lean_ctor_set(x_11, 0, x_22);
if (lean_is_scalar(x_9)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_9;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
x_26 = l_Lean_Json_compress(x_10);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("' for method '", 14, 14);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_29, x_3);
lean_dec(x_3);
x_31 = lean_mk_string_unchecked("'\n", 2, 2);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_string_append(x_32, x_24);
lean_dec(x_24);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_9)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_9;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
if (lean_is_scalar(x_9)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_9;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_4);
lean_dec(x_3);
x_239 = !lean_is_exclusive(x_6);
if (x_239 == 0)
{
return x_6;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_6, 0);
x_241 = lean_ctor_get(x_6, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_6);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
x_19 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_17, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_18);
lean_dec(x_4);
x_20 = lean_mk_string_unchecked("Expected id ", 12, 12);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
lean_dec(x_3);
x_33 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_33);
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_21 = x_35;
goto block_31;
}
case 1:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = l_Lean_JsonNumber_toString(x_36);
x_21 = x_37;
goto block_31;
}
default: 
{
lean_object* x_38; 
x_38 = lean_mk_string_unchecked("null", 4, 4);
x_21 = x_38;
goto block_31;
}
}
block_31:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked(", got id ", 9, 9);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_26);
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_10 = x_24;
x_11 = x_28;
goto block_15;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = l_Lean_JsonNumber_toString(x_29);
x_10 = x_24;
x_11 = x_30;
goto block_15;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_17);
lean_dec(x_9);
lean_inc(x_18);
x_39 = lean_apply_1(x_4, x_18);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
x_43 = l_Lean_Json_compress(x_18);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked("'\n", 2, 2);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = lean_string_append(x_46, x_41);
lean_dec(x_41);
lean_ctor_set_tag(x_39, 18);
lean_ctor_set(x_39, 0, x_47);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_8);
lean_ctor_set(x_7, 0, x_39);
return x_7;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
x_50 = l_Lean_Json_compress(x_18);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("'\n", 2, 2);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = lean_string_append(x_53, x_48);
lean_dec(x_48);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_8);
lean_ctor_set(x_7, 0, x_55);
return x_7;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_18);
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
lean_dec(x_39);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_56);
lean_ctor_set(x_7, 0, x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_7);
lean_ctor_set(x_57, 1, x_8);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_7, 0);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_7);
x_60 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_58, x_3);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_4);
x_61 = lean_mk_string_unchecked("Expected id ", 12, 12);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_3, 0);
lean_inc(x_73);
lean_dec(x_3);
x_74 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_74);
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_62 = x_76;
goto block_72;
}
case 1:
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
lean_dec(x_3);
x_78 = l_Lean_JsonNumber_toString(x_77);
x_62 = x_78;
goto block_72;
}
default: 
{
lean_object* x_79; 
x_79 = lean_mk_string_unchecked("null", 4, 4);
x_62 = x_79;
goto block_72;
}
}
block_72:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(", got id ", 9, 9);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
x_67 = lean_mk_string_unchecked("\"", 1, 1);
lean_inc(x_67);
x_68 = lean_string_append(x_67, x_66);
lean_dec(x_66);
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_10 = x_65;
x_11 = x_69;
goto block_15;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_58, 0);
lean_inc(x_70);
lean_dec(x_58);
x_71 = l_Lean_JsonNumber_toString(x_70);
x_10 = x_65;
x_11 = x_71;
goto block_15;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_58);
lean_dec(x_9);
lean_inc(x_59);
x_80 = lean_apply_1(x_4, x_59);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_3);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
x_84 = l_Lean_Json_compress(x_59);
x_85 = lean_string_append(x_83, x_84);
lean_dec(x_84);
x_86 = lean_mk_string_unchecked("'\n", 2, 2);
x_87 = lean_string_append(x_85, x_86);
lean_dec(x_86);
x_88 = lean_string_append(x_87, x_81);
lean_dec(x_81);
if (lean_is_scalar(x_82)) {
 x_89 = lean_alloc_ctor(18, 1, 0);
} else {
 x_89 = x_82;
 lean_ctor_set_tag(x_89, 18);
}
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_8);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_59);
x_91 = lean_ctor_get(x_80, 0);
lean_inc(x_91);
lean_dec(x_80);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_8);
return x_93;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_mk_string_unchecked("Expected JSON-RPC response, got: '", 34, 34);
x_95 = l_Lean_Json_instToJsonStructured;
x_96 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_97 = lean_mk_string_unchecked("2.0", 3, 3);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_7, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_7, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_7, 2);
lean_inc(x_112);
lean_dec(x_7);
x_113 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_110);
if (x_126 == 0)
{
lean_ctor_set_tag(x_110, 3);
x_114 = x_110;
goto block_125;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_110, 0);
lean_inc(x_127);
lean_dec(x_110);
x_128 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_114 = x_128;
goto block_125;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_110);
if (x_129 == 0)
{
lean_ctor_set_tag(x_110, 2);
x_114 = x_110;
goto block_125;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_110, 0);
lean_inc(x_130);
lean_dec(x_110);
x_131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_114 = x_131;
goto block_125;
}
}
block_125:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("method", 6, 6);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_111);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("params", 6, 6);
x_123 = l_Lean_Json_opt___redArg(x_95, x_122, x_112);
x_124 = l_List_appendTR(lean_box(0), x_121, x_123);
x_100 = x_124;
goto block_109;
}
}
case 1:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_7, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_7, 1);
lean_inc(x_133);
lean_dec(x_7);
x_134 = lean_mk_string_unchecked("method", 6, 6);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_132);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked("params", 6, 6);
x_138 = l_Lean_Json_opt___redArg(x_95, x_137, x_133);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_100 = x_139;
goto block_109;
}
case 2:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_7, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_7, 1);
lean_inc(x_141);
lean_dec(x_7);
x_142 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_140);
if (x_151 == 0)
{
lean_ctor_set_tag(x_140, 3);
x_143 = x_140;
goto block_150;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_140, 0);
lean_inc(x_152);
lean_dec(x_140);
x_153 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_143 = x_153;
goto block_150;
}
}
else
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_140);
if (x_154 == 0)
{
lean_ctor_set_tag(x_140, 2);
x_143 = x_140;
goto block_150;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_140, 0);
lean_inc(x_155);
lean_dec(x_140);
x_156 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_143 = x_156;
goto block_150;
}
}
block_150:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("result", 6, 6);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_141);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_148);
x_100 = x_149;
goto block_109;
}
}
default: 
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_181; lean_object* x_182; 
x_157 = lean_ctor_get(x_7, 0);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_159 = lean_ctor_get(x_7, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_7, 2);
lean_inc(x_160);
lean_dec(x_7);
x_161 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_161, 0, lean_box(0));
x_181 = lean_mk_string_unchecked("id", 2, 2);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_157);
if (x_247 == 0)
{
lean_ctor_set_tag(x_157, 3);
x_182 = x_157;
goto block_246;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_157, 0);
lean_inc(x_248);
lean_dec(x_157);
x_249 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_182 = x_249;
goto block_246;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_157);
if (x_250 == 0)
{
lean_ctor_set_tag(x_157, 2);
x_182 = x_157;
goto block_246;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_157, 0);
lean_inc(x_251);
lean_dec(x_157);
x_252 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_182 = x_252;
goto block_246;
}
}
block_180:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_mk_string_unchecked("message", 7, 7);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_159);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_166);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_mk_string_unchecked("data", 4, 4);
x_174 = l_Lean_Json_opt___redArg(x_161, x_173, x_160);
x_175 = l_List_appendTR(lean_box(0), x_172, x_174);
x_176 = l_Lean_Json_mkObj(x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_162);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_170);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_163);
lean_ctor_set(x_179, 1, x_178);
x_100 = x_179;
goto block_109;
}
block_246:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_mk_string_unchecked("error", 5, 5);
x_185 = lean_mk_string_unchecked("code", 4, 4);
switch (x_158) {
case 0:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_unsigned_to_nat(32700u);
x_187 = lean_nat_to_int(x_186);
x_188 = lean_int_neg(x_187);
lean_dec(x_187);
x_189 = l_Lean_JsonNumber_fromInt(x_188);
x_190 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_190;
goto block_180;
}
case 1:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_unsigned_to_nat(32600u);
x_192 = lean_nat_to_int(x_191);
x_193 = lean_int_neg(x_192);
lean_dec(x_192);
x_194 = l_Lean_JsonNumber_fromInt(x_193);
x_195 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_195;
goto block_180;
}
case 2:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_unsigned_to_nat(32601u);
x_197 = lean_nat_to_int(x_196);
x_198 = lean_int_neg(x_197);
lean_dec(x_197);
x_199 = l_Lean_JsonNumber_fromInt(x_198);
x_200 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_200;
goto block_180;
}
case 3:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_unsigned_to_nat(32602u);
x_202 = lean_nat_to_int(x_201);
x_203 = lean_int_neg(x_202);
lean_dec(x_202);
x_204 = l_Lean_JsonNumber_fromInt(x_203);
x_205 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_205;
goto block_180;
}
case 4:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_unsigned_to_nat(32603u);
x_207 = lean_nat_to_int(x_206);
x_208 = lean_int_neg(x_207);
lean_dec(x_207);
x_209 = l_Lean_JsonNumber_fromInt(x_208);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_210;
goto block_180;
}
case 5:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_unsigned_to_nat(32002u);
x_212 = lean_nat_to_int(x_211);
x_213 = lean_int_neg(x_212);
lean_dec(x_212);
x_214 = l_Lean_JsonNumber_fromInt(x_213);
x_215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_215;
goto block_180;
}
case 6:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_unsigned_to_nat(32001u);
x_217 = lean_nat_to_int(x_216);
x_218 = lean_int_neg(x_217);
lean_dec(x_217);
x_219 = l_Lean_JsonNumber_fromInt(x_218);
x_220 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_220;
goto block_180;
}
case 7:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_unsigned_to_nat(32801u);
x_222 = lean_nat_to_int(x_221);
x_223 = lean_int_neg(x_222);
lean_dec(x_222);
x_224 = l_Lean_JsonNumber_fromInt(x_223);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_225;
goto block_180;
}
case 8:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_unsigned_to_nat(32800u);
x_227 = lean_nat_to_int(x_226);
x_228 = lean_int_neg(x_227);
lean_dec(x_227);
x_229 = l_Lean_JsonNumber_fromInt(x_228);
x_230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_230;
goto block_180;
}
case 9:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_unsigned_to_nat(32900u);
x_232 = lean_nat_to_int(x_231);
x_233 = lean_int_neg(x_232);
lean_dec(x_232);
x_234 = l_Lean_JsonNumber_fromInt(x_233);
x_235 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_235;
goto block_180;
}
case 10:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_unsigned_to_nat(32901u);
x_237 = lean_nat_to_int(x_236);
x_238 = lean_int_neg(x_237);
lean_dec(x_237);
x_239 = l_Lean_JsonNumber_fromInt(x_238);
x_240 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_240;
goto block_180;
}
default: 
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_unsigned_to_nat(32902u);
x_242 = lean_nat_to_int(x_241);
x_243 = lean_int_neg(x_242);
lean_dec(x_242);
x_244 = l_Lean_JsonNumber_fromInt(x_243);
x_245 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_162 = x_184;
x_163 = x_183;
x_164 = x_185;
x_165 = x_245;
goto block_180;
}
}
}
}
}
block_109:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Json_mkObj(x_101);
x_103 = l_Lean_Json_compress(x_102);
x_104 = lean_string_append(x_94, x_103);
lean_dec(x_103);
x_105 = lean_mk_string_unchecked("'", 1, 1);
x_106 = lean_string_append(x_104, x_105);
lean_dec(x_105);
x_107 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_8);
return x_108;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(1, 2, 0);
} else {
 x_14 = x_9;
 lean_ctor_set_tag(x_14, 1);
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
else
{
uint8_t x_253; 
lean_dec(x_4);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_6);
if (x_253 == 0)
{
return x_6;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_6, 0);
x_255 = lean_ctor_get(x_6, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_6);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readResponseAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 4);
x_3 = x_9;
goto block_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_3 = x_12;
goto block_7;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_ctor_set_tag(x_9, 5);
x_3 = x_9;
goto block_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_3 = x_15;
goto block_7;
}
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_mk_string_unchecked("jsonrpc", 7, 7);
x_5 = lean_mk_string_unchecked("2.0", 3, 3);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
lean_ctor_set_tag(x_13, 3);
x_17 = x_13;
goto block_28;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_17 = x_31;
goto block_28;
}
}
case 1:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
lean_ctor_set_tag(x_13, 2);
x_17 = x_13;
goto block_28;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_17 = x_34;
goto block_28;
}
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
x_17 = x_35;
goto block_28;
}
}
block_28:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("method", 6, 6);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("params", 6, 6);
x_26 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_25, x_15);
x_27 = l_List_appendTR(lean_box(0), x_24, x_26);
x_8 = x_27;
goto block_12;
}
}
case 1:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_mk_string_unchecked("method", 6, 6);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_39);
x_41 = lean_mk_string_unchecked("params", 6, 6);
x_42 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_41, x_38);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
x_8 = x_43;
goto block_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
x_46 = lean_mk_string_unchecked("method", 6, 6);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked("params", 6, 6);
x_50 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_49, x_45);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_8 = x_51;
goto block_12;
}
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_54 = x_2;
} else {
 lean_dec_ref(x_2);
 x_54 = lean_box(0);
}
x_55 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_52)) {
case 0:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
lean_ctor_set_tag(x_52, 3);
x_56 = x_52;
goto block_63;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
lean_dec(x_52);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_56 = x_66;
goto block_63;
}
}
case 1:
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_ctor_set_tag(x_52, 2);
x_56 = x_52;
goto block_63;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
lean_dec(x_52);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_56 = x_69;
goto block_63;
}
}
default: 
{
lean_object* x_70; 
x_70 = lean_box(0);
x_56 = x_70;
goto block_63;
}
}
block_63:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
 lean_ctor_set_tag(x_57, 0);
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("result", 6, 6);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_8 = x_62;
goto block_12;
}
}
default: 
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_94; lean_object* x_95; 
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 2);
lean_inc(x_74);
lean_dec(x_2);
x_94 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_71)) {
case 0:
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_71);
if (x_160 == 0)
{
lean_ctor_set_tag(x_71, 3);
x_95 = x_71;
goto block_159;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_71, 0);
lean_inc(x_161);
lean_dec(x_71);
x_162 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_95 = x_162;
goto block_159;
}
}
case 1:
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_71);
if (x_163 == 0)
{
lean_ctor_set_tag(x_71, 2);
x_95 = x_71;
goto block_159;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_71, 0);
lean_inc(x_164);
lean_dec(x_71);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_95 = x_165;
goto block_159;
}
}
default: 
{
lean_object* x_166; 
x_166 = lean_box(0);
x_95 = x_166;
goto block_159;
}
}
block_93:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("message", 7, 7);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_73);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked("data", 4, 4);
x_87 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(x_86, x_74);
lean_dec(x_74);
x_88 = l_List_appendTR(lean_box(0), x_85, x_87);
x_89 = l_Lean_Json_mkObj(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_77);
lean_ctor_set(x_92, 1, x_91);
x_8 = x_92;
goto block_12;
}
block_159:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_mk_string_unchecked("error", 5, 5);
x_98 = lean_mk_string_unchecked("code", 4, 4);
switch (x_72) {
case 0:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_unsigned_to_nat(32700u);
x_100 = lean_nat_to_int(x_99);
x_101 = lean_int_neg(x_100);
lean_dec(x_100);
x_102 = l_Lean_JsonNumber_fromInt(x_101);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_103;
goto block_93;
}
case 1:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_unsigned_to_nat(32600u);
x_105 = lean_nat_to_int(x_104);
x_106 = lean_int_neg(x_105);
lean_dec(x_105);
x_107 = l_Lean_JsonNumber_fromInt(x_106);
x_108 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_108;
goto block_93;
}
case 2:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_unsigned_to_nat(32601u);
x_110 = lean_nat_to_int(x_109);
x_111 = lean_int_neg(x_110);
lean_dec(x_110);
x_112 = l_Lean_JsonNumber_fromInt(x_111);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_113;
goto block_93;
}
case 3:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_unsigned_to_nat(32602u);
x_115 = lean_nat_to_int(x_114);
x_116 = lean_int_neg(x_115);
lean_dec(x_115);
x_117 = l_Lean_JsonNumber_fromInt(x_116);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_118;
goto block_93;
}
case 4:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_unsigned_to_nat(32603u);
x_120 = lean_nat_to_int(x_119);
x_121 = lean_int_neg(x_120);
lean_dec(x_120);
x_122 = l_Lean_JsonNumber_fromInt(x_121);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_123;
goto block_93;
}
case 5:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_unsigned_to_nat(32002u);
x_125 = lean_nat_to_int(x_124);
x_126 = lean_int_neg(x_125);
lean_dec(x_125);
x_127 = l_Lean_JsonNumber_fromInt(x_126);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_128;
goto block_93;
}
case 6:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_unsigned_to_nat(32001u);
x_130 = lean_nat_to_int(x_129);
x_131 = lean_int_neg(x_130);
lean_dec(x_130);
x_132 = l_Lean_JsonNumber_fromInt(x_131);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_133;
goto block_93;
}
case 7:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_unsigned_to_nat(32801u);
x_135 = lean_nat_to_int(x_134);
x_136 = lean_int_neg(x_135);
lean_dec(x_135);
x_137 = l_Lean_JsonNumber_fromInt(x_136);
x_138 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_138;
goto block_93;
}
case 8:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_unsigned_to_nat(32800u);
x_140 = lean_nat_to_int(x_139);
x_141 = lean_int_neg(x_140);
lean_dec(x_140);
x_142 = l_Lean_JsonNumber_fromInt(x_141);
x_143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_143;
goto block_93;
}
case 9:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_unsigned_to_nat(32900u);
x_145 = lean_nat_to_int(x_144);
x_146 = lean_int_neg(x_145);
lean_dec(x_145);
x_147 = l_Lean_JsonNumber_fromInt(x_146);
x_148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_148;
goto block_93;
}
case 10:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_unsigned_to_nat(32901u);
x_150 = lean_nat_to_int(x_149);
x_151 = lean_int_neg(x_150);
lean_dec(x_150);
x_152 = l_Lean_JsonNumber_fromInt(x_151);
x_153 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_153;
goto block_93;
}
default: 
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_unsigned_to_nat(32902u);
x_155 = lean_nat_to_int(x_154);
x_156 = lean_int_neg(x_155);
lean_dec(x_155);
x_157 = l_Lean_JsonNumber_fromInt(x_156);
x_158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_75 = x_98;
x_76 = x_97;
x_77 = x_96;
x_78 = x_158;
goto block_93;
}
}
}
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
x_11 = l_IO_FS_Stream_writeJson(x_1, x_10, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_12);
x_13 = lean_box(0);
x_7 = x_13;
goto block_10;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
x_7 = x_12;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_7 = x_16;
goto block_10;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_IO_FS_Stream_writeMessage(x_2, x_8, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeRequest___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_11);
x_12 = lean_box(0);
x_6 = x_12;
goto block_9;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
x_6 = x_11;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_6 = x_15;
goto block_9;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeMessage(x_2, x_7, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeNotification___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeMessage(x_2, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponse___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_8 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
x_9 = l_IO_FS_Stream_writeMessage(x_1, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeResponseError(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
x_8 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_apply_1(x_1, x_15);
lean_ctor_set(x_12, 0, x_16);
x_8 = x_12;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_apply_1(x_1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_8 = x_19;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_6);
x_10 = l_IO_FS_Stream_writeMessage(x_2, x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponseErrorWithData___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonRpc_instInhabitedRequestID = _init_l_Lean_JsonRpc_instInhabitedRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID);
l_Lean_JsonRpc_instBEqRequestID = _init_l_Lean_JsonRpc_instBEqRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instBEqRequestID);
l_Lean_JsonRpc_instOrdRequestID = _init_l_Lean_JsonRpc_instOrdRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instOrdRequestID);
l_Lean_JsonRpc_instToStringRequestID = _init_l_Lean_JsonRpc_instToStringRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID);
l_Lean_JsonRpc_instInhabitedErrorCode = _init_l_Lean_JsonRpc_instInhabitedErrorCode();
l_Lean_JsonRpc_instBEqErrorCode = _init_l_Lean_JsonRpc_instBEqErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instBEqErrorCode);
l_Lean_JsonRpc_instFromJsonErrorCode = _init_l_Lean_JsonRpc_instFromJsonErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode);
l_Lean_JsonRpc_instToJsonErrorCode = _init_l_Lean_JsonRpc_instToJsonErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode);
l_Lean_JsonRpc_instInhabitedMessage = _init_l_Lean_JsonRpc_instInhabitedMessage();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedMessage);
l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage = _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage();
lean_mark_persistent(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage);
l_Lean_JsonRpc_instCoeStringRequestID = _init_l_Lean_JsonRpc_instCoeStringRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instCoeStringRequestID);
l_Lean_JsonRpc_instCoeJsonNumberRequestID = _init_l_Lean_JsonRpc_instCoeJsonNumberRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instCoeJsonNumberRequestID);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp);
l_Lean_JsonRpc_instLTRequestID = _init_l_Lean_JsonRpc_instLTRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instLTRequestID);
l_Lean_JsonRpc_instFromJsonRequestID = _init_l_Lean_JsonRpc_instFromJsonRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID);
l_Lean_JsonRpc_instToJsonRequestID = _init_l_Lean_JsonRpc_instToJsonRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonRequestID);
l_Lean_JsonRpc_instToJsonMessage = _init_l_Lean_JsonRpc_instToJsonMessage();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage);
l_Lean_JsonRpc_instFromJsonMessage = _init_l_Lean_JsonRpc_instFromJsonMessage();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
