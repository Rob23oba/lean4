// Lean compiler output
// Module: Lean.Data.Lsp.Communication
// Imports: Init.System.IO Lean.Data.JsonRpc
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_string_dec_eq(x_1, x_2);
x_4 = l_instDecidableNot___redArg(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_byte_size(x_1);
lean_inc(x_8);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_inc(x_8);
x_10 = l_Substring_prevn(x_9, x_6, x_8);
lean_dec(x_9);
x_11 = lean_string_utf8_extract(x_1, x_10, x_8);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("\r\n", 2, 2);
x_13 = lean_string_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_mk_string_unchecked(": ", 2, 2);
x_16 = lean_string_dec_eq(x_15, x_2);
lean_dec(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_extract(x_1, x_7, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = l_String_splitOnAux(x_17, x_15, x_7, x_7, x_7, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_15);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_21);
x_24 = l_String_intercalate(x_15, x_21);
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 1, x_24);
lean_ctor_set(x_21, 0, x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_21);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_1);
x_31 = lean_box(0);
return x_31;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("command", 7, 7);
lean_inc(x_5);
x_7 = l_Lean_Json_getObjVal_x3f(x_5, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("seq_num", 7, 7);
x_11 = l_Lean_Json_getObjVal_x3f(x_5, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_11);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_apply_1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_instDecidableEqPos(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_mk_string_unchecked("\r\n", 2, 2);
x_12 = lean_string_dec_eq(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_1);
lean_inc(x_6);
x_14 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_mk_string_unchecked("Invalid header field: ", 22, 22);
x_16 = l_String_quote(x_6);
lean_dec(x_6);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unsigned_to_nat(120u);
x_19 = lean_format_pretty(x_17, x_18, x_9, x_9);
x_20 = lean_string_append(x_15, x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_22 = lean_mk_string_unchecked("A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 ", 175, 175);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_4);
lean_dec(x_6);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1, x_7);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_dec(x_24);
return x_25;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_1);
x_34 = lean_mk_string_unchecked("Stream was closed", 17, 17);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_35);
return x_4;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_string_utf8_byte_size(x_36);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_instDecidableEqPos(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_mk_string_unchecked("\r\n", 2, 2);
x_42 = lean_string_dec_eq(x_36, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_36);
x_43 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_36);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_1);
lean_inc(x_36);
x_44 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_mk_string_unchecked("Invalid header field: ", 22, 22);
x_46 = l_String_quote(x_36);
lean_dec(x_36);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_unsigned_to_nat(120u);
x_49 = lean_format_pretty(x_47, x_48, x_39, x_39);
x_50 = lean_string_append(x_45, x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_37);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_36);
x_53 = lean_mk_string_unchecked("A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 ", 175, 175);
x_54 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_37);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_36);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1, x_37);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_dec(x_56);
return x_57;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_36);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_37);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_36);
lean_dec(x_1);
x_65 = lean_mk_string_unchecked("Stream was closed", 17, 17);
x_66 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_37);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_4);
if (x_68 == 0)
{
return x_4;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_4, 0);
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_4);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_dec_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_mk_string_unchecked(", ", 2, 2);
x_8 = lean_string_append(x_1, x_7);
x_9 = lean_mk_string_unchecked("(", 1, 1);
x_10 = lean_string_append(x_9, x_5);
x_11 = lean_string_append(x_10, x_7);
lean_dec(x_7);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_mk_string_unchecked(")", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_8, x_14);
lean_dec(x_14);
x_1 = x_15;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_mk_string_unchecked("[", 1, 1);
x_8 = lean_mk_string_unchecked("(", 1, 1);
x_9 = lean_string_append(x_8, x_5);
x_10 = lean_mk_string_unchecked(", ", 2, 2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_mk_string_unchecked(")", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_7, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("]", 1, 1);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_mk_string_unchecked("[", 1, 1);
x_22 = lean_mk_string_unchecked("(", 1, 1);
x_23 = lean_string_append(x_22, x_19);
x_24 = lean_mk_string_unchecked(", ", 2, 2);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_25, x_20);
x_27 = lean_mk_string_unchecked(")", 1, 1);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_string_append(x_21, x_28);
lean_dec(x_28);
x_30 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_29, x_3);
x_31 = lean_unsigned_to_nat(93u);
x_32 = l_Char_ofNat(x_31);
x_33 = lean_string_push(x_30, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_mk_string_unchecked("Content-Length", 14, 14);
x_7 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_6, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked("No Content-Length field in header: ", 35, 35);
x_9 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_5);
lean_dec(x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = l_String_toNat_x3f(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_mk_string_unchecked("Content-Length header field value '", 35, 35);
x_16 = lean_string_append(x_15, x_13);
lean_dec(x_13);
x_17 = lean_mk_string_unchecked("' is not a Nat", 14, 14);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_19; 
lean_free_object(x_7);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_21 = l_String_toNat_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_mk_string_unchecked("Content-Length header field value '", 35, 35);
x_23 = lean_string_append(x_22, x_20);
lean_dec(x_20);
x_24 = lean_mk_string_unchecked("' is not a Nat", 14, 14);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_26);
return x_3;
}
else
{
lean_object* x_27; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_30 = lean_mk_string_unchecked("Content-Length", 14, 14);
x_31 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_30, x_28);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_mk_string_unchecked("No Content-Length field in header: ", 35, 35);
x_33 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_28);
lean_dec(x_28);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
x_39 = l_String_toNat_x3f(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_mk_string_unchecked("Content-Length header field value '", 35, 35);
x_41 = lean_string_append(x_40, x_37);
lean_dec(x_37);
x_42 = lean_mk_string_unchecked("' is not a Nat", 14, 14);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
if (lean_is_scalar(x_38)) {
 x_44 = lean_alloc_ctor(18, 1, 0);
} else {
 x_44 = x_38;
 lean_ctor_set_tag(x_44, 18);
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_38);
lean_dec(x_37);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_29);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
return x_3;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at_____private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_11; 
lean_inc(x_1);
x_11 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_IO_FS_Stream_readMessage(x_1, x_12, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_15;
x_4 = x_16;
goto block_10;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_3 = x_17;
x_4 = x_18;
goto block_10;
}
block_10:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_mk_string_unchecked("Cannot read LSP message: ", 25, 25);
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_14, x_2, x_3, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_17;
x_6 = x_18;
goto block_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_5 = x_19;
x_6 = x_20;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_mk_string_unchecked("Cannot read LSP request: ", 25, 25);
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspRequestAs___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_14, x_2, x_3, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_17;
x_6 = x_18;
goto block_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_5 = x_19;
x_6 = x_20;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_mk_string_unchecked("Cannot read LSP notification: ", 30, 30);
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspNotificationAs___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; 
lean_inc(x_1);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_14, x_2, x_3, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_17;
x_6 = x_18;
goto block_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_5 = x_19;
x_6 = x_20;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_mk_string_unchecked("Cannot read LSP response: ", 26, 26);
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspResponseAs___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_25)) {
case 0:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
lean_ctor_set_tag(x_25, 3);
x_29 = x_25;
goto block_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_29 = x_43;
goto block_40;
}
}
case 1:
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
lean_ctor_set_tag(x_25, 2);
x_29 = x_25;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_25, 0);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_29 = x_46;
goto block_40;
}
}
default: 
{
lean_object* x_47; 
x_47 = lean_box(0);
x_29 = x_47;
goto block_40;
}
}
block_40:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked("method", 6, 6);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("params", 6, 6);
x_38 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_37, x_27);
x_39 = l_List_appendTR(lean_box(0), x_36, x_38);
x_8 = x_39;
goto block_24;
}
}
case 1:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_mk_string_unchecked("method", 6, 6);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_52);
lean_ctor_set(x_2, 0, x_51);
x_53 = lean_mk_string_unchecked("params", 6, 6);
x_54 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_53, x_50);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_54);
x_8 = x_55;
goto block_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
x_58 = lean_mk_string_unchecked("method", 6, 6);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("params", 6, 6);
x_62 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_61, x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_8 = x_63;
goto block_24;
}
}
case 2:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_66 = x_2;
} else {
 lean_dec_ref(x_2);
 x_66 = lean_box(0);
}
x_67 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_64)) {
case 0:
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
lean_ctor_set_tag(x_64, 3);
x_68 = x_64;
goto block_75;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
lean_dec(x_64);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_68 = x_78;
goto block_75;
}
}
case 1:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_64);
if (x_79 == 0)
{
lean_ctor_set_tag(x_64, 2);
x_68 = x_64;
goto block_75;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_64, 0);
lean_inc(x_80);
lean_dec(x_64);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_68 = x_81;
goto block_75;
}
}
default: 
{
lean_object* x_82; 
x_82 = lean_box(0);
x_68 = x_82;
goto block_75;
}
}
block_75:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
 lean_ctor_set_tag(x_69, 0);
}
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("result", 6, 6);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_73);
x_8 = x_74;
goto block_24;
}
}
default: 
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_106; lean_object* x_107; 
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
lean_dec(x_2);
x_106 = lean_mk_string_unchecked("id", 2, 2);
switch (lean_obj_tag(x_83)) {
case 0:
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_83);
if (x_172 == 0)
{
lean_ctor_set_tag(x_83, 3);
x_107 = x_83;
goto block_171;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_83, 0);
lean_inc(x_173);
lean_dec(x_83);
x_174 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_107 = x_174;
goto block_171;
}
}
case 1:
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_83);
if (x_175 == 0)
{
lean_ctor_set_tag(x_83, 2);
x_107 = x_83;
goto block_171;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_83, 0);
lean_inc(x_176);
lean_dec(x_83);
x_177 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_107 = x_177;
goto block_171;
}
}
default: 
{
lean_object* x_178; 
x_178 = lean_box(0);
x_107 = x_178;
goto block_171;
}
}
block_105:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("message", 7, 7);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_85);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_mk_string_unchecked("data", 4, 4);
x_99 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(x_98, x_86);
lean_dec(x_86);
x_100 = l_List_appendTR(lean_box(0), x_97, x_99);
x_101 = l_Lean_Json_mkObj(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_87);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_103);
x_8 = x_104;
goto block_24;
}
block_171:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("error", 5, 5);
x_110 = lean_mk_string_unchecked("code", 4, 4);
switch (x_84) {
case 0:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_unsigned_to_nat(32700u);
x_112 = lean_nat_to_int(x_111);
x_113 = lean_int_neg(x_112);
lean_dec(x_112);
x_114 = l_Lean_JsonNumber_fromInt(x_113);
x_115 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_115;
goto block_105;
}
case 1:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_unsigned_to_nat(32600u);
x_117 = lean_nat_to_int(x_116);
x_118 = lean_int_neg(x_117);
lean_dec(x_117);
x_119 = l_Lean_JsonNumber_fromInt(x_118);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_120;
goto block_105;
}
case 2:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_unsigned_to_nat(32601u);
x_122 = lean_nat_to_int(x_121);
x_123 = lean_int_neg(x_122);
lean_dec(x_122);
x_124 = l_Lean_JsonNumber_fromInt(x_123);
x_125 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_125;
goto block_105;
}
case 3:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_unsigned_to_nat(32602u);
x_127 = lean_nat_to_int(x_126);
x_128 = lean_int_neg(x_127);
lean_dec(x_127);
x_129 = l_Lean_JsonNumber_fromInt(x_128);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_130;
goto block_105;
}
case 4:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_unsigned_to_nat(32603u);
x_132 = lean_nat_to_int(x_131);
x_133 = lean_int_neg(x_132);
lean_dec(x_132);
x_134 = l_Lean_JsonNumber_fromInt(x_133);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_135;
goto block_105;
}
case 5:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_unsigned_to_nat(32002u);
x_137 = lean_nat_to_int(x_136);
x_138 = lean_int_neg(x_137);
lean_dec(x_137);
x_139 = l_Lean_JsonNumber_fromInt(x_138);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_140;
goto block_105;
}
case 6:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_unsigned_to_nat(32001u);
x_142 = lean_nat_to_int(x_141);
x_143 = lean_int_neg(x_142);
lean_dec(x_142);
x_144 = l_Lean_JsonNumber_fromInt(x_143);
x_145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_145;
goto block_105;
}
case 7:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_unsigned_to_nat(32801u);
x_147 = lean_nat_to_int(x_146);
x_148 = lean_int_neg(x_147);
lean_dec(x_147);
x_149 = l_Lean_JsonNumber_fromInt(x_148);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_150;
goto block_105;
}
case 8:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_unsigned_to_nat(32800u);
x_152 = lean_nat_to_int(x_151);
x_153 = lean_int_neg(x_152);
lean_dec(x_152);
x_154 = l_Lean_JsonNumber_fromInt(x_153);
x_155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_155;
goto block_105;
}
case 9:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_unsigned_to_nat(32900u);
x_157 = lean_nat_to_int(x_156);
x_158 = lean_int_neg(x_157);
lean_dec(x_157);
x_159 = l_Lean_JsonNumber_fromInt(x_158);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_160;
goto block_105;
}
case 10:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_unsigned_to_nat(32901u);
x_162 = lean_nat_to_int(x_161);
x_163 = lean_int_neg(x_162);
lean_dec(x_162);
x_164 = l_Lean_JsonNumber_fromInt(x_163);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_165;
goto block_105;
}
default: 
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_unsigned_to_nat(32902u);
x_167 = lean_nat_to_int(x_166);
x_168 = lean_int_neg(x_167);
lean_dec(x_167);
x_169 = l_Lean_JsonNumber_fromInt(x_168);
x_170 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_87 = x_109;
x_88 = x_110;
x_89 = x_108;
x_90 = x_170;
goto block_105;
}
}
}
}
}
block_24:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
x_11 = l_Lean_Json_compress(x_10);
x_12 = lean_mk_string_unchecked("Content-Length: ", 16, 16);
x_13 = lean_string_utf8_byte_size(x_11);
x_14 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("\r\n\r\n", 4, 4);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
x_19 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_20 = lean_apply_2(x_18, x_19, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_1(x_22, x_21);
return x_23;
}
else
{
lean_dec(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_IO_FS_Stream_writeLspMessage(x_2, x_8, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspRequest___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_IO_FS_Stream_writeLspMessage(x_2, x_7, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspNotification___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_IO_FS_Stream_writeLspMessage(x_2, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponse___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponseError(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_IO_FS_Stream_writeLspMessage(x_2, x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
