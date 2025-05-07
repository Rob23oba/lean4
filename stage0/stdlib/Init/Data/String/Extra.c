// Lean compiler output
// Module: Init.Data.String.Extra
// Imports: Init.Data.ByteArray Init.Data.UInt.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_Iterator_remainingBytes_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_utf8DecodeChar_x3f___lam__0(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_loop___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_crlfToLf_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_loop(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8EncodeChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_find(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_foldUntil___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_crlfToLf_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__ByteArray_size_match__1_splitter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8EncodeChar(uint32_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Extra______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux___at___String_isInt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object*);
lean_object* lean_byte_array_data(lean_object*);
LEAN_EXPORT lean_object* l_String_toNat_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x21___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_find___at_____private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__ByteArray_size_match__1_splitter(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Extra______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_String_validateUTF8_loop(lean_object*, lean_object*);
lean_object* l_String_foldlAux___at___String_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_Iterator_remainingBytes_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Iterator_foldUntil(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_validateUTF8_loop___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT lean_object* l_panic___at___String_toNat_x21_spec__0(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_toSubstring_x27(lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___String_toNat_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_instInhabitedNat;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21(lean_object* x_1) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_instDecidableEqPos(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_String_anyAux___at___String_isInt_spec__0(x_1, x_1, x_14, x_15);
lean_dec(x_14);
if (x_17 == 0)
{
goto block_13;
}
else
{
if (x_16 == 0)
{
goto block_9;
}
else
{
goto block_13;
}
}
}
else
{
lean_dec(x_14);
goto block_9;
}
block_9:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
x_3 = lean_mk_string_unchecked("String.toNat!", 13, 13);
x_4 = lean_unsigned_to_nat(33u);
x_5 = lean_unsigned_to_nat(4u);
x_6 = lean_mk_string_unchecked("Nat expected", 12, 12);
x_7 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_panic___at___String_toNat_x21_spec__0(x_7);
return x_8;
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_1);
x_12 = l_String_foldlAux___at___String_toNat_x3f_spec__0(x_1, x_11, x_10, x_10);
lean_dec(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_String_toNat_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toNat_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_utf8DecodeChar_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_9; 
x_9 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_11 = lean_byte_array_fget(x_1, x_2);
x_12 = lean_unsigned_to_nat(128u);
x_13 = lean_uint8_of_nat(x_12);
x_14 = lean_uint8_land(x_11, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_uint8_of_nat(x_15);
x_17 = lean_uint8_dec_eq(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_18 = lean_unsigned_to_nat(224u);
x_19 = lean_uint8_of_nat(x_18);
x_20 = lean_uint8_land(x_11, x_19);
x_21 = lean_unsigned_to_nat(192u);
x_22 = lean_uint8_of_nat(x_21);
x_23 = lean_uint8_dec_eq(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_24 = lean_unsigned_to_nat(240u);
x_25 = lean_uint8_of_nat(x_24);
x_26 = lean_uint8_land(x_11, x_25);
x_27 = lean_uint8_dec_eq(x_26, x_19);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_28 = lean_unsigned_to_nat(248u);
x_29 = lean_uint8_of_nat(x_28);
x_30 = lean_uint8_land(x_11, x_29);
x_31 = lean_uint8_dec_eq(x_30, x_25);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_2, x_33);
x_35 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
x_36 = lean_box(0);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_nat_add(x_2, x_37);
x_39 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_34);
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_add(x_2, x_41);
x_43 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_34);
x_44 = lean_box(0);
return x_44;
}
else
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_88; uint8_t x_89; 
x_45 = lean_byte_array_fget(x_1, x_34);
lean_dec(x_34);
x_46 = lean_byte_array_fget(x_1, x_38);
lean_dec(x_38);
x_47 = lean_byte_array_fget(x_1, x_42);
lean_dec(x_42);
x_88 = lean_uint8_land(x_45, x_22);
x_89 = lean_uint8_dec_eq(x_88, x_13);
if (x_89 == 0)
{
x_48 = x_89;
goto block_87;
}
else
{
uint8_t x_90; uint8_t x_91; 
x_90 = lean_uint8_land(x_46, x_22);
x_91 = lean_uint8_dec_eq(x_90, x_13);
x_48 = x_91;
goto block_87;
}
block_87:
{
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
return x_49;
}
else
{
uint8_t x_50; uint8_t x_51; 
x_50 = lean_uint8_land(x_47, x_22);
x_51 = lean_uint8_dec_eq(x_50, x_13);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
return x_52;
}
else
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; uint32_t x_56; lean_object* x_57; uint32_t x_58; uint32_t x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; uint32_t x_63; lean_object* x_64; uint32_t x_65; uint32_t x_66; uint32_t x_67; uint8_t x_68; uint32_t x_69; lean_object* x_70; uint32_t x_71; uint32_t x_72; uint32_t x_73; uint8_t x_74; uint32_t x_75; uint32_t x_76; lean_object* x_77; uint32_t x_78; uint8_t x_79; 
x_53 = lean_unsigned_to_nat(7u);
x_54 = lean_uint8_of_nat(x_53);
x_55 = lean_uint8_land(x_11, x_54);
x_56 = lean_uint8_to_uint32(x_55);
x_57 = lean_unsigned_to_nat(18u);
x_58 = lean_uint32_of_nat(x_57);
x_59 = lean_uint32_shift_left(x_56, x_58);
x_60 = lean_unsigned_to_nat(63u);
x_61 = lean_uint8_of_nat(x_60);
x_62 = lean_uint8_land(x_45, x_61);
x_63 = lean_uint8_to_uint32(x_62);
x_64 = lean_unsigned_to_nat(12u);
x_65 = lean_uint32_of_nat(x_64);
x_66 = lean_uint32_shift_left(x_63, x_65);
x_67 = lean_uint32_lor(x_59, x_66);
x_68 = lean_uint8_land(x_46, x_61);
x_69 = lean_uint8_to_uint32(x_68);
x_70 = lean_unsigned_to_nat(6u);
x_71 = lean_uint32_of_nat(x_70);
x_72 = lean_uint32_shift_left(x_69, x_71);
x_73 = lean_uint32_lor(x_67, x_72);
x_74 = lean_uint8_land(x_47, x_61);
x_75 = lean_uint8_to_uint32(x_74);
x_76 = lean_uint32_lor(x_73, x_75);
x_77 = lean_unsigned_to_nat(65536u);
x_78 = lean_uint32_of_nat(x_77);
x_79 = lean_uint32_dec_le(x_78, x_76);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_box(0);
return x_80;
}
else
{
lean_object* x_81; uint32_t x_82; uint8_t x_83; 
x_81 = lean_unsigned_to_nat(1114112u);
x_82 = lean_uint32_of_nat(x_81);
x_83 = lean_uint32_dec_lt(x_76, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_box(0);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_box_uint32(x_76);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_2, x_92);
x_94 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_93);
x_95 = lean_box(0);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_unsigned_to_nat(2u);
x_97 = lean_nat_add(x_2, x_96);
x_98 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_97);
lean_dec(x_93);
x_99 = lean_box(0);
return x_99;
}
else
{
uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_138; uint8_t x_139; 
x_100 = lean_byte_array_fget(x_1, x_93);
lean_dec(x_93);
x_101 = lean_byte_array_fget(x_1, x_97);
lean_dec(x_97);
x_138 = lean_uint8_land(x_100, x_22);
x_139 = lean_uint8_dec_eq(x_138, x_13);
if (x_139 == 0)
{
x_102 = x_139;
goto block_137;
}
else
{
uint8_t x_140; uint8_t x_141; 
x_140 = lean_uint8_land(x_101, x_22);
x_141 = lean_uint8_dec_eq(x_140, x_13);
x_102 = x_141;
goto block_137;
}
block_137:
{
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_box(0);
return x_103;
}
else
{
lean_object* x_104; uint8_t x_105; uint8_t x_106; uint32_t x_107; lean_object* x_108; uint32_t x_109; uint32_t x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint32_t x_114; lean_object* x_115; uint32_t x_116; uint32_t x_117; uint32_t x_118; uint8_t x_119; uint32_t x_120; uint32_t x_121; lean_object* x_122; uint32_t x_123; uint8_t x_124; 
x_104 = lean_unsigned_to_nat(15u);
x_105 = lean_uint8_of_nat(x_104);
x_106 = lean_uint8_land(x_11, x_105);
x_107 = lean_uint8_to_uint32(x_106);
x_108 = lean_unsigned_to_nat(12u);
x_109 = lean_uint32_of_nat(x_108);
x_110 = lean_uint32_shift_left(x_107, x_109);
x_111 = lean_unsigned_to_nat(63u);
x_112 = lean_uint8_of_nat(x_111);
x_113 = lean_uint8_land(x_100, x_112);
x_114 = lean_uint8_to_uint32(x_113);
x_115 = lean_unsigned_to_nat(6u);
x_116 = lean_uint32_of_nat(x_115);
x_117 = lean_uint32_shift_left(x_114, x_116);
x_118 = lean_uint32_lor(x_110, x_117);
x_119 = lean_uint8_land(x_101, x_112);
x_120 = lean_uint8_to_uint32(x_119);
x_121 = lean_uint32_lor(x_118, x_120);
x_122 = lean_unsigned_to_nat(2048u);
x_123 = lean_uint32_of_nat(x_122);
x_124 = lean_uint32_dec_le(x_123, x_121);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_box(0);
return x_125;
}
else
{
lean_object* x_126; uint32_t x_127; uint8_t x_128; 
x_126 = lean_unsigned_to_nat(55296u);
x_127 = lean_uint32_of_nat(x_126);
x_128 = lean_uint32_dec_lt(x_121, x_127);
if (x_128 == 0)
{
lean_object* x_129; uint32_t x_130; uint8_t x_131; 
x_129 = lean_unsigned_to_nat(57343u);
x_130 = lean_uint32_of_nat(x_129);
x_131 = lean_uint32_dec_lt(x_130, x_121);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
return x_132;
}
else
{
lean_object* x_133; uint32_t x_134; uint8_t x_135; 
x_133 = lean_unsigned_to_nat(1114112u);
x_134 = lean_uint32_of_nat(x_133);
x_135 = lean_uint32_dec_lt(x_121, x_134);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
return x_136;
}
else
{
x_3 = x_118;
x_4 = x_120;
goto block_8;
}
}
}
else
{
x_3 = x_118;
x_4 = x_120;
goto block_8;
}
}
}
}
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_2, x_142);
x_144 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_143);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_143);
x_145 = lean_box(0);
return x_145;
}
else
{
uint8_t x_146; uint8_t x_147; uint8_t x_148; 
x_146 = lean_byte_array_fget(x_1, x_143);
lean_dec(x_143);
x_147 = lean_uint8_land(x_146, x_22);
x_148 = lean_uint8_dec_eq(x_147, x_13);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
return x_149;
}
else
{
lean_object* x_150; uint8_t x_151; uint8_t x_152; uint32_t x_153; lean_object* x_154; uint32_t x_155; uint32_t x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; uint32_t x_160; uint32_t x_161; uint32_t x_162; uint8_t x_163; 
x_150 = lean_unsigned_to_nat(31u);
x_151 = lean_uint8_of_nat(x_150);
x_152 = lean_uint8_land(x_11, x_151);
x_153 = lean_uint8_to_uint32(x_152);
x_154 = lean_unsigned_to_nat(6u);
x_155 = lean_uint32_of_nat(x_154);
x_156 = lean_uint32_shift_left(x_153, x_155);
x_157 = lean_unsigned_to_nat(63u);
x_158 = lean_uint8_of_nat(x_157);
x_159 = lean_uint8_land(x_146, x_158);
x_160 = lean_uint8_to_uint32(x_159);
x_161 = lean_uint32_lor(x_156, x_160);
x_162 = lean_uint32_of_nat(x_12);
x_163 = lean_uint32_dec_le(x_162, x_161);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_box(0);
return x_164;
}
else
{
lean_object* x_165; uint32_t x_166; uint8_t x_167; 
x_165 = lean_unsigned_to_nat(55296u);
x_166 = lean_uint32_of_nat(x_165);
x_167 = lean_uint32_dec_lt(x_161, x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_box(0);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_box_uint32(x_161);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
}
}
}
else
{
uint32_t x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_uint8_to_uint32(x_11);
x_172 = lean_box_uint32(x_171);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
block_8:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_uint32_lor(x_3, x_4);
x_6 = lean_box_uint32(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_utf8DecodeChar_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_utf8DecodeChar_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_utf8DecodeChar_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_validateUTF8_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_String_utf8DecodeChar_x3f(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unbox_uint32(x_9);
lean_dec(x_9);
x_11 = l_Char_utf8Size(x_10);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_validateUTF8_loop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_validateUTF8_loop(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_validateUTF8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_string_validate_utf8(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_10; uint8_t x_11; 
x_10 = lean_byte_array_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_12; 
x_12 = l_String_utf8DecodeChar_x3f(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint32_t x_14; 
x_13 = lean_unsigned_to_nat(65u);
x_14 = l_Char_ofNat(x_13);
x_4 = x_14;
goto block_9;
}
else
{
lean_object* x_15; uint32_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_unbox_uint32(x_15);
lean_dec(x_15);
x_4 = x_16;
goto block_9;
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Char_utf8Size(x_4);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_string_push(x_3, x_4);
x_2 = x_6;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_fromUTF8_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_string_from_utf8_unchecked(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_string_validate_utf8(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_from_utf8_unchecked(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_fromUTF8_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_string_validate_utf8(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
x_5 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
x_6 = lean_unsigned_to_nat(128u);
x_7 = lean_unsigned_to_nat(47u);
x_8 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___redArg(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_string_from_utf8_unchecked(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_String_fromUTF8_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_fromUTF8_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_utf8EncodeChar(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(127u);
x_3 = lean_uint32_of_nat(x_2);
x_4 = lean_uint32_dec_le(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(2047u);
x_6 = lean_uint32_of_nat(x_5);
x_7 = lean_uint32_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(65535u);
x_9 = lean_uint32_of_nat(x_8);
x_10 = lean_uint32_dec_le(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint32_t x_22; uint32_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; uint32_t x_32; uint32_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_11 = lean_unsigned_to_nat(18u);
x_12 = lean_uint32_of_nat(x_11);
x_13 = lean_uint32_shift_right(x_1, x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = lean_unsigned_to_nat(7u);
x_16 = lean_uint8_of_nat(x_15);
x_17 = lean_uint8_land(x_14, x_16);
x_18 = lean_unsigned_to_nat(240u);
x_19 = lean_uint8_of_nat(x_18);
x_20 = lean_uint8_lor(x_17, x_19);
x_21 = lean_unsigned_to_nat(12u);
x_22 = lean_uint32_of_nat(x_21);
x_23 = lean_uint32_shift_right(x_1, x_22);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_unsigned_to_nat(63u);
x_26 = lean_uint8_of_nat(x_25);
x_27 = lean_uint8_land(x_24, x_26);
x_28 = lean_unsigned_to_nat(128u);
x_29 = lean_uint8_of_nat(x_28);
x_30 = lean_uint8_lor(x_27, x_29);
x_31 = lean_unsigned_to_nat(6u);
x_32 = lean_uint32_of_nat(x_31);
x_33 = lean_uint32_shift_right(x_1, x_32);
x_34 = lean_uint32_to_uint8(x_33);
x_35 = lean_uint8_land(x_34, x_26);
x_36 = lean_uint8_lor(x_35, x_29);
x_37 = lean_uint32_to_uint8(x_1);
x_38 = lean_uint8_land(x_37, x_26);
x_39 = lean_uint8_lor(x_38, x_29);
x_40 = lean_box(0);
x_41 = lean_box(x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_box(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_box(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_box(x_20);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; uint32_t x_50; uint32_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; uint32_t x_60; uint32_t x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_49 = lean_unsigned_to_nat(12u);
x_50 = lean_uint32_of_nat(x_49);
x_51 = lean_uint32_shift_right(x_1, x_50);
x_52 = lean_uint32_to_uint8(x_51);
x_53 = lean_unsigned_to_nat(15u);
x_54 = lean_uint8_of_nat(x_53);
x_55 = lean_uint8_land(x_52, x_54);
x_56 = lean_unsigned_to_nat(224u);
x_57 = lean_uint8_of_nat(x_56);
x_58 = lean_uint8_lor(x_55, x_57);
x_59 = lean_unsigned_to_nat(6u);
x_60 = lean_uint32_of_nat(x_59);
x_61 = lean_uint32_shift_right(x_1, x_60);
x_62 = lean_uint32_to_uint8(x_61);
x_63 = lean_unsigned_to_nat(63u);
x_64 = lean_uint8_of_nat(x_63);
x_65 = lean_uint8_land(x_62, x_64);
x_66 = lean_unsigned_to_nat(128u);
x_67 = lean_uint8_of_nat(x_66);
x_68 = lean_uint8_lor(x_65, x_67);
x_69 = lean_uint32_to_uint8(x_1);
x_70 = lean_uint8_land(x_69, x_64);
x_71 = lean_uint8_lor(x_70, x_67);
x_72 = lean_box(0);
x_73 = lean_box(x_71);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_box(x_68);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_box(x_58);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; uint32_t x_80; uint32_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_79 = lean_unsigned_to_nat(6u);
x_80 = lean_uint32_of_nat(x_79);
x_81 = lean_uint32_shift_right(x_1, x_80);
x_82 = lean_uint32_to_uint8(x_81);
x_83 = lean_unsigned_to_nat(31u);
x_84 = lean_uint8_of_nat(x_83);
x_85 = lean_uint8_land(x_82, x_84);
x_86 = lean_unsigned_to_nat(192u);
x_87 = lean_uint8_of_nat(x_86);
x_88 = lean_uint8_lor(x_85, x_87);
x_89 = lean_uint32_to_uint8(x_1);
x_90 = lean_unsigned_to_nat(63u);
x_91 = lean_uint8_of_nat(x_90);
x_92 = lean_uint8_land(x_89, x_91);
x_93 = lean_unsigned_to_nat(128u);
x_94 = lean_uint8_of_nat(x_93);
x_95 = lean_uint8_lor(x_92, x_94);
x_96 = lean_box(0);
x_97 = lean_box(x_95);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_box(x_88);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_uint32_to_uint8(x_1);
x_102 = lean_box(0);
x_103 = lean_box(x_101);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
LEAN_EXPORT lean_object* l_String_utf8EncodeChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_String_utf8EncodeChar(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_toUTF8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_to_utf8(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__ByteArray_size_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_byte_array_data(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__ByteArray_size_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Extra_0__ByteArray_size_match__1_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_string_get_byte_fast(x_1, x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_Iterator_remainingBytes_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_Iterator_remainingBytes_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Extra_0__String_Iterator_remainingBytes_match__1_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Extra______macroRules__tacticDecreasing__trivial__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticDecreasing_trivial", 24, 24);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_9 = lean_ctor_get(x_2, 5);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("withReducible", 13, 13);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
x_20 = lean_mk_string_unchecked("with_reducible", 14, 14);
lean_inc(x_12);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_22);
x_24 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_25 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_24);
x_26 = lean_mk_string_unchecked("null", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("apply", 5, 5);
lean_inc(x_28);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_28);
lean_inc(x_12);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_mk_string_unchecked("String.Iterator.sizeOf_next_lt_of_hasNext", 41, 41);
x_32 = l_String_toSubstring_x27(x_31);
x_33 = lean_mk_string_unchecked("String", 6, 6);
x_34 = lean_mk_string_unchecked("Iterator", 8, 8);
x_35 = lean_mk_string_unchecked("sizeOf_next_lt_of_hasNext", 25, 25);
x_36 = l_Lean_Name_mkStr3(x_33, x_34, x_35);
lean_inc(x_36);
x_37 = l_Lean_addMacroScope(x_14, x_36, x_13);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_12);
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_41);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node2(x_12, x_29, x_30, x_42);
x_44 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_12);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_46);
x_47 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_46);
lean_inc(x_12);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_46);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_47, x_48);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node3(x_12, x_27, x_43, x_45, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_25, x_50);
lean_inc(x_12);
x_52 = l_Lean_Syntax_node1(x_12, x_23, x_51);
x_53 = l_Lean_Syntax_node2(x_12, x_19, x_21, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_String___aux__Init__Data__String__Extra______macroRules__tacticDecreasing__trivial__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticDecreasing_trivial", 24, 24);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_9 = lean_ctor_get(x_2, 5);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_SourceInfo_fromRef(x_9, x_11);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Parser", 6, 6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = lean_mk_string_unchecked("withReducible", 13, 13);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
x_20 = lean_mk_string_unchecked("with_reducible", 14, 14);
lean_inc(x_12);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_23 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_22);
x_24 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_25 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_24);
x_26 = lean_mk_string_unchecked("null", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("apply", 5, 5);
lean_inc(x_28);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_28);
lean_inc(x_12);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_mk_string_unchecked("String.Iterator.sizeOf_next_lt_of_atEnd", 39, 39);
x_32 = l_String_toSubstring_x27(x_31);
x_33 = lean_mk_string_unchecked("String", 6, 6);
x_34 = lean_mk_string_unchecked("Iterator", 8, 8);
x_35 = lean_mk_string_unchecked("sizeOf_next_lt_of_atEnd", 23, 23);
x_36 = l_Lean_Name_mkStr3(x_33, x_34, x_35);
lean_inc(x_36);
x_37 = l_Lean_addMacroScope(x_14, x_36, x_13);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_12);
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_41);
lean_inc(x_12);
x_43 = l_Lean_Syntax_node2(x_12, x_29, x_30, x_42);
x_44 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_12);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("assumption", 10, 10);
lean_inc(x_46);
x_47 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_46);
lean_inc(x_12);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_46);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_47, x_48);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node3(x_12, x_27, x_43, x_45, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_25, x_50);
lean_inc(x_12);
x_52 = l_Lean_Syntax_node1(x_12, x_23, x_51);
x_53 = l_Lean_Syntax_node2(x_12, x_19, x_21, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_le(x_5, x_4);
lean_dec(x_5);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_string_utf8_get(x_3, x_4);
x_8 = lean_box_uint32(x_7);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_string_utf8_next(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_14);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_string_utf8_next(x_3, x_4);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_1 = x_17;
goto _start;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_foldUntil___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_nat_dec_le(x_6, x_5);
lean_dec(x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_string_utf8_get(x_4, x_5);
x_9 = lean_box_uint32(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_2(x_3, x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_16);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
x_1 = x_20;
x_2 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_1);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_String_Iterator_foldUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Iterator_foldUntil___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_13 = lean_string_utf8_byte_size(x_4);
x_14 = lean_nat_dec_le(x_13, x_5);
lean_dec(x_13);
if (x_14 == 0)
{
uint32_t x_15; lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_15 = lean_string_utf8_get(x_4, x_5);
x_16 = lean_unsigned_to_nat(32u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(9u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_15, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(10u);
x_23 = l_Char_ofNat(x_22);
x_24 = l_instDecidableEqChar(x_15, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_nat_dec_le(x_2, x_3);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_2);
x_28 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_26, x_3);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_26, x_2);
lean_dec(x_2);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_31, x_3);
return x_32;
}
}
else
{
goto block_12;
}
}
else
{
goto block_12;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(0, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_nat_dec_le(x_6, x_5);
lean_dec(x_6);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_4, x_5);
x_9 = lean_unsigned_to_nat(10u);
x_10 = l_Char_ofNat(x_9);
x_11 = l_instDecidableEqChar(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_12);
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_string_utf8_next(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_1, x_15, x_2);
return x_16;
}
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = lean_string_utf8_byte_size(x_17);
x_20 = lean_nat_dec_le(x_19, x_18);
lean_dec(x_19);
if (x_20 == 0)
{
uint32_t x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_21 = lean_string_utf8_get(x_17, x_18);
x_22 = lean_unsigned_to_nat(10u);
x_23 = l_Char_ofNat(x_22);
x_24 = l_instDecidableEqChar(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_string_utf8_next(x_17, x_18);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_1 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_string_utf8_next(x_17, x_18);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_29, x_30, x_2);
return x_31;
}
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Iterator_find___at_____private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_le(x_4, x_3);
lean_dec(x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_2, x_3);
x_7 = lean_unsigned_to_nat(10u);
x_8 = l_Char_ofNat(x_7);
x_9 = l_instDecidableEqChar(x_6, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_string_utf8_next(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_13);
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_string_utf8_next(x_2, x_3);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_1 = x_16;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_String_Iterator_find___at_____private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_8);
x_9 = lean_string_length(x_1);
lean_dec(x_1);
x_10 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_4, x_2, x_9);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_string_utf8_next(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_string_length(x_1);
lean_dec(x_1);
x_16 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(x_14, x_2, x_15);
lean_dec(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(x_1, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_string_utf8_byte_size(x_8);
x_12 = lean_nat_dec_le(x_11, x_9);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint32_t x_18; lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_13 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
x_18 = lean_string_utf8_get(x_8, x_9);
x_19 = lean_unsigned_to_nat(32u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(9u);
x_23 = l_Char_ofNat(x_22);
x_24 = l_instDecidableEqChar(x_18, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_25 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(x_1, x_3, x_4);
return x_25;
}
else
{
lean_dec(x_3);
goto block_17;
}
}
else
{
lean_dec(x_3);
goto block_17;
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next(x_8, x_9);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_le(x_7, x_6);
lean_dec(x_7);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get(x_5, x_6);
x_10 = lean_unsigned_to_nat(10u);
x_11 = l_Char_ofNat(x_10);
x_12 = l_instDecidableEqChar(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
lean_ctor_set(x_2, 1, x_13);
x_14 = lean_string_push(x_3, x_9);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_string_utf8_next(x_5, x_6);
lean_dec(x_6);
lean_ctor_set(x_2, 1, x_16);
x_17 = lean_string_push(x_3, x_11);
lean_inc(x_1);
x_18 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(x_1, x_1, x_2, x_17);
return x_18;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_21 = lean_string_utf8_byte_size(x_19);
x_22 = lean_nat_dec_le(x_21, x_20);
lean_dec(x_21);
if (x_22 == 0)
{
uint32_t x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_23 = lean_string_utf8_get(x_19, x_20);
x_24 = lean_unsigned_to_nat(10u);
x_25 = l_Char_ofNat(x_24);
x_26 = l_instDecidableEqChar(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_string_utf8_next(x_19, x_20);
lean_dec(x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_string_push(x_3, x_23);
x_2 = x_28;
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_string_utf8_next(x_19, x_20);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_string_push(x_3, x_25);
lean_inc(x_1);
x_34 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(x_1, x_1, x_32, x_33);
return x_34;
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_1);
x_6 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(x_1, x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_removeLeadingSpaces(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(x_2, x_1);
return x_5;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_25; 
x_6 = lean_string_utf8_get_fast(x_1, x_4);
x_7 = lean_string_utf8_next_fast(x_1, x_4);
x_25 = lean_string_utf8_at_end(x_1, x_7);
if (x_25 == 0)
{
x_8 = x_5;
goto block_24;
}
else
{
x_8 = x_25;
goto block_24;
}
block_24:
{
uint8_t x_9; 
x_9 = l_instDecidableNot___redArg(x_8);
if (x_9 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(13u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_6, x_12);
if (x_13 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
uint32_t x_15; lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_15 = lean_string_utf8_get(x_1, x_7);
x_16 = lean_unsigned_to_nat(10u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_15, x_17);
if (x_18 == 0)
{
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_string_append(x_2, x_20);
lean_dec(x_20);
x_22 = lean_string_utf8_next_fast(x_1, x_7);
x_2 = x_21;
x_3 = x_7;
x_4 = x_22;
goto _start;
}
}
}
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_instDecidableEqPos(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_string_utf8_extract(x_1, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_string_append(x_2, x_28);
lean_dec(x_28);
return x_29;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_crlfToLf_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_crlfToLf_go(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_crlfToLf___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_crlfToLf(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Extra(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
