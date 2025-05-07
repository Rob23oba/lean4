// Lean compiler output
// Module: Lean.Parser.StrInterpolation
// Imports: Lean.Parser.Basic
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
uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t);
lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_interpolatedStr_docString__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr(lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAtomicInfo(lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_mkNodeToken(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withoutPosition(lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharForStrInterpolant(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(123u);
x_3 = l_Char_ofNat(x_2);
x_4 = l_instDecidableEqChar(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Parser_isQuotableCharDefault(x_1);
return x_5;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharForStrInterpolant___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Parser_isQuotableCharForStrInterpolant(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn_parse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_2, x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_string_utf8_get(x_2, x_7);
x_10 = lean_string_utf8_next(x_2, x_7);
lean_dec(x_7);
x_11 = l_Lean_Parser_ParserState_setPos(x_6, x_10);
lean_dec(x_6);
x_12 = lean_unsigned_to_nat(34u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(92u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(123u);
x_19 = l_Char_ofNat(x_18);
x_20 = l_instDecidableEqChar(x_9, x_19);
if (x_20 == 0)
{
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_22 = lean_mk_string_unchecked("interpolatedStrLitKind", 22, 22);
x_23 = l_Lean_Name_mkStr1(x_22);
lean_inc(x_5);
x_24 = l_Lean_Parser_mkNodeToken(x_23, x_4, x_5, x_11);
lean_inc(x_1);
lean_inc(x_5);
x_25 = lean_apply_2(x_1, x_5, x_24);
x_41 = lean_ctor_get(x_25, 4);
lean_inc(x_41);
x_42 = lean_box(0);
x_43 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lean_Parser_ParserState_mkNode_spec__0(x_41, x_42);
if (x_43 == 0)
{
x_26 = x_20;
goto block_40;
}
else
{
x_26 = x_17;
goto block_40;
}
block_40:
{
if (x_26 == 0)
{
lean_object* x_27; uint32_t x_28; lean_object* x_29; uint32_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
x_28 = lean_string_utf8_get(x_2, x_27);
x_29 = lean_unsigned_to_nat(125u);
x_30 = l_Char_ofNat(x_29);
x_31 = l_instDecidableEqChar(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_mk_string_unchecked("'}'", 3, 3);
x_33 = l_Lean_Parser_ParserState_mkError(x_25, x_32);
x_34 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
x_35 = l_Lean_Name_mkStr1(x_34);
x_36 = l_Lean_Parser_ParserState_mkNode(x_33, x_35, x_3);
lean_dec(x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_string_utf8_next(x_2, x_27);
x_38 = l_Lean_Parser_ParserState_setPos(x_25, x_37);
lean_dec(x_25);
x_4 = x_27;
x_6 = x_38;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_alloc_closure((void*)(l_Lean_Parser_isQuotableCharForStrInterpolant___boxed), 1, 0);
x_45 = lean_box(x_17);
x_46 = lean_alloc_closure((void*)(l_Lean_Parser_quotedCharCoreFn___boxed), 4, 2);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
x_47 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn_parse), 6, 4);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_2);
lean_closure_set(x_47, 2, x_3);
lean_closure_set(x_47, 3, x_4);
x_48 = l_Lean_Parser_andthenFn(x_46, x_47, x_5, x_11);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_mk_string_unchecked("interpolatedStrLitKind", 22, 22);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = l_Lean_Parser_mkNodeToken(x_50, x_4, x_5, x_11);
x_52 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = l_Lean_Parser_ParserState_mkNode(x_51, x_53, x_3);
lean_dec(x_3);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_mk_string_unchecked("unterminated string literal", 27, 27);
x_56 = l_Lean_Parser_ParserState_mkError(x_6, x_55);
x_57 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = l_Lean_Parser_ParserState_mkNode(x_56, x_58, x_3);
lean_dec(x_3);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_string_utf8_at_end(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_11 = lean_string_utf8_get(x_8, x_9);
x_12 = lean_unsigned_to_nat(34u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_11, x_13);
if (x_14 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
goto block_6;
}
else
{
if (x_10 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Parser_ParserState_stackSize(x_3);
x_16 = l_Lean_Parser_ParserState_next(x_3, x_8, x_9);
lean_dec(x_3);
x_17 = l_Lean_Parser_interpolatedStrFn_parse(x_1, x_8, x_15, x_9, x_2, x_16);
return x_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
goto block_6;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_18);
return x_19;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("interpolated string", 19, 19);
x_5 = l_Lean_Parser_ParserState_mkError(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStrNoAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
x_3 = l_Lean_Parser_mkAtomicInfo(x_2);
x_4 = l_Lean_Parser_withoutPosition(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Parser_interpolatedStr_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_mk_string_unchecked("The parser `interpolatedStr(p)` parses a string literal like `\"foo\"` (see `str`), but the string\nmay also contain `{}` escapes, and within the escapes the parser `p` is used. For example,\n`interpolatedStr(term)` will parse `\"foo {2 + 2}\"`, where `2 + 2` is parsed as a term rather than\nas a string. Note that the full Lean term grammar is available here, including string literals,\nso for example `\"foo {\"bar\" ++ \"baz\"}\"` is a legal interpolated string (which evaluates to\n`foo barbaz`).\n\nThis parser has arity 1, and returns a `interpolatedStrKind` with an odd number of arguments,\nalternating between chunks of literal text and results from `p`. The literal chunks contain\nuninterpreted substrings of the input. For example, `\"foo\\n{2 + 2}\"` would have three arguments:\nan atom `\"foo\\n{`, the parsed `2 + 2` term, and then the atom `}\"`. ", 840, 840);
x_7 = l_Lean_addBuiltinDocString(x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_interpolatedStr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
x_3 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = lean_unbox(x_5);
x_8 = lean_unbox(x_6);
x_9 = l_Lean_Parser_mkAntiquot(x_2, x_4, x_7, x_8);
x_10 = l_Lean_Parser_mkAtomicInfo(x_2);
x_11 = l_Lean_Parser_withoutPosition(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Parser_interpolatedStrFn), 3, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Parser_withAntiquot(x_9, x_14);
return x_15;
}
}
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Parser_interpolatedStr_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
