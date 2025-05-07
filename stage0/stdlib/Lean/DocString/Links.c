// Lean compiler output
// Module: Lean.DocString.Links
// Imports: Lean.Syntax
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_rewriteManualLinks_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore_urlChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_getManualRoot___boxed(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0(uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_manualRoot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot;
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_rewriteManualLinksCore_lookingAt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_rewriteManualLinksCore_urlChar(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_manual_get_root(lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_validateBuiltinDocString_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_String_Iterator_forward(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rewriteManualLinks_spec__1(lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_validateBuiltinDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_String_substrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_rewriteManualLinks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore_lookingAt___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore_rw(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rewriteManualLinks_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Links_0__Lean_getManualRoot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_manual_get_root(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("https://lean-lang.org/doc/reference/latest/", 43, 43);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_manualRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("LEAN_MANUAL_ROOT", 16, 16);
x_3 = lean_io_getenv(x_2, x_1);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_box(0);
x_23 = lean_manual_get_root(x_22);
x_24 = lean_string_utf8_byte_size(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_instDecidableEqPos(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
x_7 = x_23;
goto block_21;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
x_27 = lean_mk_string_unchecked("https://lean-lang.org/doc/reference/latest/", 43, 43);
x_7 = x_27;
goto block_21;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_7 = x_28;
goto block_21;
}
block_21:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_mk_string_unchecked("/", 1, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_byte_size(x_7);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_inc(x_10);
x_13 = l_Substring_prevn(x_12, x_11, x_10);
lean_dec(x_12);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_string_utf8_byte_size(x_8);
lean_inc(x_8);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Substring_beq(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_string_append(x_7, x_8);
lean_dec(x_8);
if (lean_is_scalar(x_6)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_6;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_8);
if (lean_is_scalar(x_6)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_6;
}
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_rewriteManualLinksCore_urlChar(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_64; uint8_t x_72; lean_object* x_80; uint32_t x_81; uint8_t x_82; 
x_80 = lean_unsigned_to_nat(65u);
x_81 = lean_uint32_of_nat(x_80);
x_82 = lean_uint32_dec_le(x_81, x_1);
if (x_82 == 0)
{
x_72 = x_82;
goto block_79;
}
else
{
lean_object* x_83; uint32_t x_84; uint8_t x_85; 
x_83 = lean_unsigned_to_nat(90u);
x_84 = lean_uint32_of_nat(x_83);
x_85 = lean_uint32_dec_le(x_1, x_84);
x_72 = x_85;
goto block_79;
}
block_63:
{
if (x_2 == 0)
{
lean_object* x_3; uint32_t x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(45u);
x_4 = l_Char_ofNat(x_3);
x_5 = l_instDecidableEqChar(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(46u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(95u);
x_10 = l_Char_ofNat(x_9);
x_11 = l_instDecidableEqChar(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(126u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(58u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(47u);
x_19 = l_Char_ofNat(x_18);
x_20 = l_instDecidableEqChar(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(63u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(35u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_1, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(91u);
x_28 = l_Char_ofNat(x_27);
x_29 = l_instDecidableEqChar(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(93u);
x_31 = l_Char_ofNat(x_30);
x_32 = l_instDecidableEqChar(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint32_t x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(64u);
x_34 = l_Char_ofNat(x_33);
x_35 = l_instDecidableEqChar(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint32_t x_37; uint8_t x_38; 
x_36 = lean_unsigned_to_nat(33u);
x_37 = l_Char_ofNat(x_36);
x_38 = l_instDecidableEqChar(x_1, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(36u);
x_40 = l_Char_ofNat(x_39);
x_41 = l_instDecidableEqChar(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint32_t x_43; uint8_t x_44; 
x_42 = lean_unsigned_to_nat(38u);
x_43 = l_Char_ofNat(x_42);
x_44 = l_instDecidableEqChar(x_1, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(39u);
x_46 = l_Char_ofNat(x_45);
x_47 = l_instDecidableEqChar(x_1, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(42u);
x_49 = l_Char_ofNat(x_48);
x_50 = l_instDecidableEqChar(x_1, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint32_t x_52; uint8_t x_53; 
x_51 = lean_unsigned_to_nat(43u);
x_52 = l_Char_ofNat(x_51);
x_53 = l_instDecidableEqChar(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint32_t x_55; uint8_t x_56; 
x_54 = lean_unsigned_to_nat(44u);
x_55 = l_Char_ofNat(x_54);
x_56 = l_instDecidableEqChar(x_1, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint32_t x_58; uint8_t x_59; 
x_57 = lean_unsigned_to_nat(59u);
x_58 = l_Char_ofNat(x_57);
x_59 = l_instDecidableEqChar(x_1, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint32_t x_61; uint8_t x_62; 
x_60 = lean_unsigned_to_nat(61u);
x_61 = l_Char_ofNat(x_60);
x_62 = l_instDecidableEqChar(x_1, x_61);
return x_62;
}
else
{
return x_59;
}
}
else
{
return x_56;
}
}
else
{
return x_53;
}
}
else
{
return x_50;
}
}
else
{
return x_47;
}
}
else
{
return x_44;
}
}
else
{
return x_41;
}
}
else
{
return x_38;
}
}
else
{
return x_35;
}
}
else
{
return x_32;
}
}
else
{
return x_29;
}
}
else
{
return x_26;
}
}
else
{
return x_23;
}
}
else
{
return x_20;
}
}
else
{
return x_17;
}
}
else
{
return x_14;
}
}
else
{
return x_11;
}
}
else
{
return x_8;
}
}
else
{
return x_5;
}
}
else
{
return x_2;
}
}
block_71:
{
if (x_64 == 0)
{
lean_object* x_65; uint32_t x_66; uint8_t x_67; 
x_65 = lean_unsigned_to_nat(48u);
x_66 = lean_uint32_of_nat(x_65);
x_67 = lean_uint32_dec_le(x_66, x_1);
if (x_67 == 0)
{
x_2 = x_67;
goto block_63;
}
else
{
lean_object* x_68; uint32_t x_69; uint8_t x_70; 
x_68 = lean_unsigned_to_nat(57u);
x_69 = lean_uint32_of_nat(x_68);
x_70 = lean_uint32_dec_le(x_1, x_69);
x_2 = x_70;
goto block_63;
}
}
else
{
return x_64;
}
}
block_79:
{
if (x_72 == 0)
{
lean_object* x_73; uint32_t x_74; uint8_t x_75; 
x_73 = lean_unsigned_to_nat(97u);
x_74 = lean_uint32_of_nat(x_73);
x_75 = lean_uint32_dec_le(x_74, x_1);
if (x_75 == 0)
{
x_64 = x_75;
goto block_71;
}
else
{
lean_object* x_76; uint32_t x_77; uint8_t x_78; 
x_76 = lean_unsigned_to_nat(122u);
x_77 = lean_uint32_of_nat(x_76);
x_78 = lean_uint32_dec_le(x_1, x_77);
x_64 = x_78;
goto block_71;
}
}
else
{
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore_urlChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_rewriteManualLinksCore_urlChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_rewriteManualLinksCore_lookingAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = l_String_substrEq(x_3, x_4, x_1, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore_lookingAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_rewriteManualLinksCore_lookingAt(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_mk_string_unchecked(", ", 2, 2);
x_6 = lean_string_append(x_1, x_5);
lean_dec(x_5);
x_7 = lean_string_append(x_6, x_3);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_string_append(x_5, x_4);
x_7 = lean_mk_string_unchecked("]", 1, 1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_mk_string_unchecked("[", 1, 1);
x_11 = lean_string_append(x_10, x_9);
x_12 = l_List_foldl___at___List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0_spec__0(x_11, x_3);
x_13 = lean_unsigned_to_nat(93u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_string_push(x_12, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore_rw(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_mk_string_unchecked("/", 1, 1);
x_36 = lean_mk_string_unchecked("", 0, 0);
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_box(0);
x_40 = l_String_splitOnAux(x_1, x_35, x_38, x_38, x_38, x_39);
lean_dec(x_35);
lean_dec(x_1);
if (lean_obj_tag(x_40) == 0)
{
goto block_11;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_18 = x_41;
x_19 = x_42;
goto block_34;
}
}
else
{
lean_object* x_43; 
lean_dec(x_35);
x_43 = lean_box(0);
x_18 = x_1;
x_19 = x_43;
goto block_34;
}
block_8:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_mk_string_unchecked("Unknown documentation type '", 28, 28);
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_mk_string_unchecked("'. Expected 'section'.", 22, 22);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_mk_string_unchecked("Missing documentation type", 26, 26);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_mk_string_unchecked("Expected one item after 'section', but got ", 43, 43);
x_14 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_34:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_mk_string_unchecked("section", 7, 7);
x_21 = lean_string_dec_eq(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_mk_string_unchecked("", 0, 0);
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_19);
x_2 = x_18;
goto block_8;
}
else
{
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_22);
goto block_11;
}
else
{
lean_dec(x_19);
x_2 = x_22;
goto block_8;
}
}
}
else
{
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
x_12 = x_19;
goto block_17;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_string_utf8_byte_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_instDecidableEqPos(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_mk_string_unchecked("find/\?domain=Verso.Genre.Manual.section&name=", 45, 45);
x_30 = lean_string_append(x_29, x_25);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
x_32 = lean_mk_string_unchecked("Empty section ID", 16, 16);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_dec(x_24);
x_12 = x_19;
goto block_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___Lean_rewriteManualLinksCore_rw_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_string_utf8_byte_size(x_8);
lean_dec(x_8);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_77; uint8_t x_83; 
x_24 = lean_ctor_get(x_7, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
x_26 = lean_string_utf8_get_fast(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_27 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_inc(x_27);
lean_inc(x_21);
lean_ctor_set(x_7, 1, x_27);
x_83 = l_Lean_rewriteManualLinksCore_urlChar(x_26);
if (x_83 == 0)
{
x_77 = x_83;
goto block_82;
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_string_utf8_byte_size(x_21);
x_85 = lean_nat_dec_le(x_84, x_27);
lean_dec(x_84);
if (x_85 == 0)
{
x_77 = x_83;
goto block_82;
}
else
{
goto block_76;
}
}
block_62:
{
lean_object* x_29; 
x_29 = l_Lean_rewriteManualLinksCore_rw(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
x_33 = lean_string_utf8_prev(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_34 = lean_string_utf8_prev(x_21, x_27);
lean_dec(x_27);
lean_dec(x_21);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
x_37 = lean_array_push(x_10, x_36);
x_38 = lean_string_push(x_12, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_11);
x_43 = lean_ctor_get(x_29, 0);
lean_inc(x_43);
lean_dec(x_29);
x_44 = l_Lean_manualRoot(x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_string_append(x_12, x_46);
lean_dec(x_46);
x_48 = lean_string_append(x_47, x_43);
lean_dec(x_43);
x_49 = lean_string_push(x_48, x_26);
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_string_append(x_12, x_53);
lean_dec(x_53);
x_56 = lean_string_append(x_55, x_43);
lean_dec(x_43);
x_57 = lean_string_push(x_56, x_26);
lean_inc(x_7);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_7);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
return x_61;
}
}
}
block_69:
{
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_string_utf8_extract(x_63, x_65, x_64);
lean_dec(x_64);
x_28 = x_67;
goto block_62;
}
else
{
lean_object* x_68; 
lean_dec(x_64);
x_68 = lean_mk_string_unchecked("", 0, 0);
x_28 = x_68;
goto block_62;
}
}
block_76:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_2, 0);
x_71 = lean_ctor_get(x_2, 1);
x_72 = lean_string_utf8_prev(x_21, x_27);
x_73 = lean_string_dec_eq(x_70, x_21);
x_74 = l_instDecidableNot___redArg(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = lean_nat_dec_lt(x_72, x_71);
x_63 = x_70;
x_64 = x_72;
x_65 = x_71;
x_66 = x_75;
goto block_69;
}
else
{
x_63 = x_70;
x_64 = x_72;
x_65 = x_71;
x_66 = x_74;
goto block_69;
}
}
block_82:
{
if (x_77 == 0)
{
goto block_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_27);
lean_dec(x_21);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_7);
lean_ctor_set(x_78, 1, x_12);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_11);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_10);
lean_ctor_set(x_80, 1, x_79);
x_3 = x_80;
goto _start;
}
}
}
else
{
uint32_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_131; uint8_t x_137; 
lean_dec(x_7);
x_86 = lean_string_utf8_get_fast(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_87 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_inc(x_87);
lean_inc(x_21);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_21);
lean_ctor_set(x_88, 1, x_87);
x_137 = l_Lean_rewriteManualLinksCore_urlChar(x_86);
if (x_137 == 0)
{
x_131 = x_137;
goto block_136;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_string_utf8_byte_size(x_21);
x_139 = lean_nat_dec_le(x_138, x_87);
lean_dec(x_138);
if (x_139 == 0)
{
x_131 = x_137;
goto block_136;
}
else
{
goto block_130;
}
}
block_116:
{
lean_object* x_90; 
x_90 = l_Lean_rewriteManualLinksCore_rw(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_ctor_get(x_11, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_11, 1);
lean_inc(x_93);
x_94 = lean_string_utf8_prev(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
x_95 = lean_string_utf8_prev(x_21, x_87);
lean_dec(x_87);
lean_dec(x_21);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
x_98 = lean_array_push(x_10, x_97);
x_99 = lean_string_push(x_12, x_1);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_11);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_4);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_87);
lean_dec(x_21);
lean_dec(x_11);
x_104 = lean_ctor_get(x_90, 0);
lean_inc(x_104);
lean_dec(x_90);
x_105 = l_Lean_manualRoot(x_4);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_string_append(x_12, x_106);
lean_dec(x_106);
x_110 = lean_string_append(x_109, x_104);
lean_dec(x_104);
x_111 = lean_string_push(x_110, x_86);
lean_inc(x_88);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_88);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_88);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_10);
lean_ctor_set(x_114, 1, x_113);
if (lean_is_scalar(x_108)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_108;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_107);
return x_115;
}
}
block_123:
{
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_string_utf8_extract(x_117, x_119, x_118);
lean_dec(x_118);
x_89 = x_121;
goto block_116;
}
else
{
lean_object* x_122; 
lean_dec(x_118);
x_122 = lean_mk_string_unchecked("", 0, 0);
x_89 = x_122;
goto block_116;
}
}
block_130:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_124 = lean_ctor_get(x_2, 0);
x_125 = lean_ctor_get(x_2, 1);
x_126 = lean_string_utf8_prev(x_21, x_87);
x_127 = lean_string_dec_eq(x_124, x_21);
x_128 = l_instDecidableNot___redArg(x_127);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = lean_nat_dec_lt(x_126, x_125);
x_117 = x_124;
x_118 = x_126;
x_119 = x_125;
x_120 = x_129;
goto block_123;
}
else
{
x_117 = x_124;
x_118 = x_126;
x_119 = x_125;
x_120 = x_128;
goto block_123;
}
}
block_136:
{
if (x_131 == 0)
{
goto block_130;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_87);
lean_dec(x_21);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_88);
lean_ctor_set(x_132, 1, x_12);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_11);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_10);
lean_ctor_set(x_134, 1, x_133);
x_3 = x_134;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_string_utf8_byte_size(x_5);
lean_dec(x_5);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = lean_mk_string_unchecked("lean-manual://", 14, 14);
x_22 = lean_string_utf8_get_fast(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_23 = lean_string_utf8_next_fast(x_16, x_17);
lean_dec(x_17);
lean_inc(x_23);
lean_inc(x_16);
lean_ctor_set(x_4, 1, x_23);
x_53 = lean_string_utf8_prev(x_16, x_23);
lean_inc(x_16);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_16);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_rewriteManualLinksCore_lookingAt(x_21, x_54);
lean_dec(x_21);
if (x_55 == 0)
{
if (x_10 == 0)
{
goto block_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_23);
lean_dec(x_16);
x_56 = lean_string_push(x_8, x_22);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_57);
x_1 = x_58;
goto _start;
}
}
else
{
goto block_52;
}
block_52:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_24 = lean_string_utf8_prev(x_16, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(14u);
x_27 = l_String_Iterator_forward(x_25, x_26);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0(x_22, x_27, x_30, x_2);
lean_dec(x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_34, 0);
lean_dec(x_41);
lean_ctor_set(x_34, 0, x_38);
lean_ctor_set(x_33, 0, x_36);
x_1 = x_33;
x_2 = x_35;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_36);
x_1 = x_33;
x_2 = x_35;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_48 = x_34;
} else {
 lean_dec_ref(x_34);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_49);
x_1 = x_50;
x_2 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_60; uint32_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_4);
x_60 = lean_mk_string_unchecked("lean-manual://", 14, 14);
x_61 = lean_string_utf8_get_fast(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_62 = lean_string_utf8_next_fast(x_16, x_17);
lean_dec(x_17);
lean_inc(x_62);
lean_inc(x_16);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_16);
lean_ctor_set(x_63, 1, x_62);
x_85 = lean_string_utf8_prev(x_16, x_62);
lean_inc(x_16);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_16);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_rewriteManualLinksCore_lookingAt(x_60, x_86);
lean_dec(x_60);
if (x_87 == 0)
{
if (x_10 == 0)
{
goto block_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_62);
lean_dec(x_16);
x_88 = lean_string_push(x_8, x_61);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_63);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_7);
lean_ctor_set(x_90, 1, x_89);
x_1 = x_90;
goto _start;
}
}
else
{
goto block_84;
}
block_84:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_64 = lean_string_utf8_prev(x_16, x_62);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_16);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unsigned_to_nat(14u);
x_67 = l_String_Iterator_forward(x_65, x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_7);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0(x_61, x_67, x_70, x_2);
lean_dec(x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_79);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
x_1 = x_82;
x_2 = x_75;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_string_utf8_byte_size(x_5);
lean_dec(x_5);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_19 = lean_ctor_get(x_4, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = lean_mk_string_unchecked("lean-manual://", 14, 14);
x_22 = lean_string_utf8_get_fast(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_23 = lean_string_utf8_next_fast(x_16, x_17);
lean_dec(x_17);
lean_inc(x_23);
lean_inc(x_16);
lean_ctor_set(x_4, 1, x_23);
x_53 = lean_string_utf8_prev(x_16, x_23);
lean_inc(x_16);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_16);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_rewriteManualLinksCore_lookingAt(x_21, x_54);
lean_dec(x_21);
if (x_55 == 0)
{
if (x_10 == 0)
{
goto block_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
lean_dec(x_16);
x_56 = lean_string_push(x_8, x_22);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_7);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(x_58, x_2);
return x_59;
}
}
else
{
goto block_52;
}
block_52:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_24 = lean_string_utf8_prev(x_16, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(14u);
x_27 = l_String_Iterator_forward(x_25, x_26);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0(x_22, x_27, x_30, x_2);
lean_dec(x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_34, 0);
lean_dec(x_41);
lean_ctor_set(x_34, 0, x_38);
lean_ctor_set(x_33, 0, x_36);
x_42 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(x_33, x_35);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_36);
x_45 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(x_33, x_35);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_48 = x_34;
} else {
 lean_dec_ref(x_34);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(x_50, x_35);
return x_51;
}
}
}
else
{
lean_object* x_60; uint32_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_4);
x_60 = lean_mk_string_unchecked("lean-manual://", 14, 14);
x_61 = lean_string_utf8_get_fast(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_62 = lean_string_utf8_next_fast(x_16, x_17);
lean_dec(x_17);
lean_inc(x_62);
lean_inc(x_16);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_16);
lean_ctor_set(x_63, 1, x_62);
x_85 = lean_string_utf8_prev(x_16, x_62);
lean_inc(x_16);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_16);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_rewriteManualLinksCore_lookingAt(x_60, x_86);
lean_dec(x_60);
if (x_87 == 0)
{
if (x_10 == 0)
{
goto block_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_62);
lean_dec(x_16);
x_88 = lean_string_push(x_8, x_61);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_63);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_7);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(x_90, x_2);
return x_91;
}
}
else
{
goto block_84;
}
block_84:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_64 = lean_string_utf8_prev(x_16, x_62);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_16);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unsigned_to_nat(14u);
x_67 = l_String_Iterator_forward(x_65, x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_7);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0(x_61, x_67, x_70, x_2);
lean_dec(x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_79);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1_spec__1(x_82, x_75);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinksCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__1(x_8, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_14);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_22 = x_11;
} else {
 lean_dec_ref(x_11);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_Lean_Loop_forIn_loop___at___Lean_rewriteManualLinksCore_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_rewriteManualLinks_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_mk_string_unchecked(" * ```", 6, 6);
x_14 = lean_string_utf8_extract(x_1, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("```: ", 5, 5);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_10);
lean_dec(x_10);
x_19 = lean_mk_string_unchecked("\n\n", 2, 2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_20);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_mk_string_unchecked(" * ```", 6, 6);
x_27 = lean_string_utf8_extract(x_1, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("```: ", 5, 5);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = lean_string_append(x_30, x_23);
lean_dec(x_23);
x_32 = lean_mk_string_unchecked("\n\n", 2, 2);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
x_2 = x_22;
x_3 = x_34;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rewriteManualLinks_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_rewriteManualLinks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_3 = l_Lean_rewriteManualLinksCore(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Array_isEmpty___redArg(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_mk_string_unchecked("**❌ Syntax Errors in Lean Language Reference Links**\n\nThe `lean-manual` URL scheme is used to link to the version of the Lean reference manual that\ncorresponds to this version of Lean. Errors occurred while processing the links in this documentation\ncomment:\n", 261, 259);
x_10 = lean_array_to_list(x_6);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at___Lean_rewriteManualLinks_spec__0(x_1, x_10, x_11);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("", 0, 0);
x_14 = l_List_foldl___at___Lean_rewriteManualLinks_spec__1(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_9, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("\n\n", 2, 2);
x_17 = lean_string_append(x_7, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_15);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Array_isEmpty___redArg(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_mk_string_unchecked("**❌ Syntax Errors in Lean Language Reference Links**\n\nThe `lean-manual` URL scheme is used to link to the version of the Lean reference manual that\ncorresponds to this version of Lean. Errors occurred while processing the links in this documentation\ncomment:\n", 261, 259);
x_25 = lean_array_to_list(x_21);
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___at___Lean_rewriteManualLinks_spec__0(x_1, x_25, x_26);
lean_dec(x_1);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_List_foldl___at___Lean_rewriteManualLinks_spec__1(x_28, x_27);
lean_dec(x_27);
x_30 = lean_string_append(x_24, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("\n\n", 2, 2);
x_32 = lean_string_append(x_22, x_31);
lean_dec(x_31);
x_33 = lean_string_append(x_32, x_30);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_20);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_21);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_20);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_rewriteManualLinks_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___Lean_rewriteManualLinks_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_rewriteManualLinks_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___Lean_rewriteManualLinks_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_validateBuiltinDocString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_mk_string_unchecked(" * ", 3, 3);
x_14 = lean_string_utf8_extract(x_1, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_15 = l_String_quote(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_unsigned_to_nat(120u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_format_pretty(x_16, x_17, x_18, x_18);
x_20 = lean_string_append(x_13, x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked(":\n    ", 6, 6);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_string_append(x_22, x_10);
lean_dec(x_10);
x_24 = lean_mk_string_unchecked("\n", 1, 1);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_25);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_dec(x_6);
x_31 = lean_mk_string_unchecked(" * ", 3, 3);
x_32 = lean_string_utf8_extract(x_1, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_33 = l_String_quote(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unsigned_to_nat(120u);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_format_pretty(x_34, x_35, x_36, x_36);
x_38 = lean_string_append(x_31, x_37);
lean_dec(x_37);
x_39 = lean_mk_string_unchecked(":\n    ", 6, 6);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = lean_string_append(x_40, x_28);
lean_dec(x_28);
x_42 = lean_mk_string_unchecked("\n", 1, 1);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
x_2 = x_27;
x_3 = x_44;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateBuiltinDocString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_3 = l_Lean_rewriteManualLinksCore(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_isEmpty___redArg(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("Errors in builtin documentation comment:\n", 41, 41);
x_9 = lean_array_to_list(x_6);
x_10 = lean_box(0);
x_11 = l_List_mapTR_loop___at___Lean_validateBuiltinDocString_spec__0(x_1, x_9, x_10);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_List_foldl___at___Lean_rewriteManualLinks_spec__1(x_12, x_11);
lean_dec(x_11);
x_14 = lean_string_append(x_8, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_isEmpty___redArg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_mk_string_unchecked("Errors in builtin documentation comment:\n", 41, 41);
x_22 = lean_array_to_list(x_19);
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at___Lean_validateBuiltinDocString_spec__0(x_1, x_22, x_23);
lean_dec(x_1);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = l_List_foldl___at___Lean_rewriteManualLinks_spec__1(x_25, x_24);
lean_dec(x_24);
x_27 = lean_string_append(x_21, x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_validateBuiltinDocString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___Lean_validateBuiltinDocString_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lean_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Links(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot = _init_l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot();
lean_mark_persistent(l___private_Lean_DocString_Links_0__Lean_fallbackManualRoot);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
