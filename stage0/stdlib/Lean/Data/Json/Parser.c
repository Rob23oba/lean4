// Lean compiler output
// Module: Lean.Data.Json.Parser
// Imports: Lean.Data.Json.Basic Lean.Data.RBMap Std.Internal.Parsec
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
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
uint16_t lean_uint32_to_uint16(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object*);
extern lean_object* l_System_Platform_numBits;
uint16_t lean_uint16_of_nat(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
uint16_t lean_uint16_lor(uint16_t, uint16_t);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object*);
lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_land(uint32_t, uint32_t);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint16_t lean_uint16_shift_left(uint16_t, uint16_t);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
uint32_t lean_uint16_to_uint32(uint16_t);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_Parser_hexChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_26; uint8_t x_27; lean_object* x_43; uint8_t x_44; uint32_t x_57; uint8_t x_58; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_string_utf8_get_fast(x_2, x_3);
x_12 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_12);
x_43 = lean_unsigned_to_nat(48u);
x_57 = l_Char_ofNat(x_43);
x_58 = lean_uint32_dec_le(x_57, x_11);
if (x_58 == 0)
{
x_44 = x_58;
goto block_56;
}
else
{
lean_object* x_59; uint32_t x_60; uint8_t x_61; 
x_59 = lean_unsigned_to_nat(57u);
x_60 = l_Char_ofNat(x_59);
x_61 = lean_uint32_dec_le(x_11, x_60);
x_44 = x_61;
goto block_56;
}
block_25:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_mk_string_unchecked("invalid hex character", 21, 21);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint32_t x_17; uint32_t x_18; lean_object* x_19; uint32_t x_20; uint32_t x_21; uint16_t x_22; lean_object* x_23; lean_object* x_24; 
x_17 = l_Char_ofNat(x_13);
x_18 = lean_uint32_sub(x_11, x_17);
x_19 = lean_unsigned_to_nat(10u);
x_20 = lean_uint32_of_nat(x_19);
x_21 = lean_uint32_add(x_18, x_20);
x_22 = lean_uint32_to_uint16(x_21);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
block_42:
{
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(65u);
x_29 = l_Char_ofNat(x_28);
x_30 = lean_uint32_dec_le(x_29, x_11);
if (x_30 == 0)
{
x_13 = x_28;
x_14 = x_30;
goto block_25;
}
else
{
lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(70u);
x_32 = l_Char_ofNat(x_31);
x_33 = lean_uint32_dec_le(x_11, x_32);
x_13 = x_28;
x_14 = x_33;
goto block_25;
}
}
else
{
uint32_t x_34; uint32_t x_35; lean_object* x_36; uint32_t x_37; uint32_t x_38; uint16_t x_39; lean_object* x_40; lean_object* x_41; 
x_34 = l_Char_ofNat(x_26);
x_35 = lean_uint32_sub(x_11, x_34);
x_36 = lean_unsigned_to_nat(10u);
x_37 = lean_uint32_of_nat(x_36);
x_38 = lean_uint32_add(x_35, x_37);
x_39 = lean_uint32_to_uint16(x_38);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
block_56:
{
if (x_44 == 0)
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(97u);
x_46 = l_Char_ofNat(x_45);
x_47 = lean_uint32_dec_le(x_46, x_11);
if (x_47 == 0)
{
x_26 = x_45;
x_27 = x_47;
goto block_42;
}
else
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(102u);
x_49 = l_Char_ofNat(x_48);
x_50 = lean_uint32_dec_le(x_11, x_49);
x_26 = x_45;
x_27 = x_50;
goto block_42;
}
}
else
{
uint32_t x_51; uint32_t x_52; uint16_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = l_Char_ofNat(x_43);
x_52 = lean_uint32_sub(x_11, x_51);
x_53 = lean_uint32_to_uint16(x_52);
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint32_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_78; uint8_t x_79; lean_object* x_95; uint8_t x_96; uint32_t x_109; uint8_t x_110; 
lean_dec(x_1);
x_62 = lean_string_utf8_get_fast(x_2, x_3);
x_63 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_63);
x_95 = lean_unsigned_to_nat(48u);
x_109 = l_Char_ofNat(x_95);
x_110 = lean_uint32_dec_le(x_109, x_62);
if (x_110 == 0)
{
x_96 = x_110;
goto block_108;
}
else
{
lean_object* x_111; uint32_t x_112; uint8_t x_113; 
x_111 = lean_unsigned_to_nat(57u);
x_112 = l_Char_ofNat(x_111);
x_113 = lean_uint32_dec_le(x_62, x_112);
x_96 = x_113;
goto block_108;
}
block_77:
{
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_mk_string_unchecked("invalid hex character", 21, 21);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
uint32_t x_69; uint32_t x_70; lean_object* x_71; uint32_t x_72; uint32_t x_73; uint16_t x_74; lean_object* x_75; lean_object* x_76; 
x_69 = l_Char_ofNat(x_65);
x_70 = lean_uint32_sub(x_62, x_69);
x_71 = lean_unsigned_to_nat(10u);
x_72 = lean_uint32_of_nat(x_71);
x_73 = lean_uint32_add(x_70, x_72);
x_74 = lean_uint32_to_uint16(x_73);
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
block_94:
{
if (x_79 == 0)
{
lean_object* x_80; uint32_t x_81; uint8_t x_82; 
x_80 = lean_unsigned_to_nat(65u);
x_81 = l_Char_ofNat(x_80);
x_82 = lean_uint32_dec_le(x_81, x_62);
if (x_82 == 0)
{
x_65 = x_80;
x_66 = x_82;
goto block_77;
}
else
{
lean_object* x_83; uint32_t x_84; uint8_t x_85; 
x_83 = lean_unsigned_to_nat(70u);
x_84 = l_Char_ofNat(x_83);
x_85 = lean_uint32_dec_le(x_62, x_84);
x_65 = x_80;
x_66 = x_85;
goto block_77;
}
}
else
{
uint32_t x_86; uint32_t x_87; lean_object* x_88; uint32_t x_89; uint32_t x_90; uint16_t x_91; lean_object* x_92; lean_object* x_93; 
x_86 = l_Char_ofNat(x_78);
x_87 = lean_uint32_sub(x_62, x_86);
x_88 = lean_unsigned_to_nat(10u);
x_89 = lean_uint32_of_nat(x_88);
x_90 = lean_uint32_add(x_87, x_89);
x_91 = lean_uint32_to_uint16(x_90);
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_64);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
block_108:
{
if (x_96 == 0)
{
lean_object* x_97; uint32_t x_98; uint8_t x_99; 
x_97 = lean_unsigned_to_nat(97u);
x_98 = l_Char_ofNat(x_97);
x_99 = lean_uint32_dec_le(x_98, x_62);
if (x_99 == 0)
{
x_78 = x_97;
x_79 = x_99;
goto block_94;
}
else
{
lean_object* x_100; uint32_t x_101; uint8_t x_102; 
x_100 = lean_unsigned_to_nat(102u);
x_101 = l_Char_ofNat(x_100);
x_102 = lean_uint32_dec_le(x_62, x_101);
x_78 = x_97;
x_79 = x_102;
goto block_94;
}
}
else
{
uint32_t x_103; uint32_t x_104; uint16_t x_105; lean_object* x_106; lean_object* x_107; 
x_103 = l_Char_ofNat(x_95);
x_104 = lean_uint32_sub(x_62, x_103);
x_105 = lean_uint32_to_uint16(x_104);
x_106 = lean_box(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_64);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_7; uint32_t x_8; lean_object* x_9; lean_object* x_14; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_2, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_2, 1);
lean_inc(x_112);
x_113 = lean_string_utf8_byte_size(x_111);
x_114 = lean_nat_dec_lt(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
x_115 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_2);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
else
{
lean_object* x_117; uint32_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_138; lean_object* x_151; uint32_t x_152; uint8_t x_153; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_117 = x_2;
} else {
 lean_dec_ref(x_2);
 x_117 = lean_box(0);
}
x_118 = lean_string_utf8_get_fast(x_111, x_112);
x_119 = lean_string_utf8_next_fast(x_111, x_112);
lean_dec(x_112);
lean_inc(x_119);
lean_inc(x_111);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_111);
lean_ctor_set(x_138, 1, x_119);
x_151 = lean_unsigned_to_nat(92u);
x_152 = l_Char_ofNat(x_151);
x_153 = l_instDecidableEqChar(x_118, x_152);
if (x_153 == 0)
{
if (x_114 == 0)
{
goto block_150;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
x_154 = lean_mk_string_unchecked("", 0, 0);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_138);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
else
{
goto block_150;
}
block_137:
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_string_utf8_next_fast(x_111, x_119);
lean_dec(x_119);
x_123 = lean_nat_dec_lt(x_122, x_113);
lean_dec(x_113);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_111);
x_124 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
uint32_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint32_t x_130; uint8_t x_131; 
lean_dec(x_121);
x_126 = lean_string_utf8_get_fast(x_111, x_120);
x_127 = lean_string_utf8_next_fast(x_111, x_120);
lean_dec(x_120);
if (lean_is_scalar(x_117)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_117;
}
lean_ctor_set(x_128, 0, x_111);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_unsigned_to_nat(100u);
x_130 = l_Char_ofNat(x_129);
x_131 = l_instDecidableEqChar(x_126, x_130);
if (x_131 == 0)
{
if (x_123 == 0)
{
x_14 = x_128;
goto block_110;
}
else
{
lean_object* x_132; uint32_t x_133; uint8_t x_134; 
x_132 = lean_unsigned_to_nat(68u);
x_133 = l_Char_ofNat(x_132);
x_134 = l_instDecidableEqChar(x_126, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_mk_string_unchecked("", 0, 0);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_128);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
x_14 = x_128;
goto block_110;
}
}
}
else
{
x_14 = x_128;
goto block_110;
}
}
}
block_150:
{
uint8_t x_139; 
x_139 = lean_nat_dec_lt(x_119, x_113);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
x_140 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
else
{
uint32_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint32_t x_146; uint8_t x_147; 
lean_dec(x_138);
x_142 = lean_string_utf8_get_fast(x_111, x_119);
x_143 = lean_string_utf8_next_fast(x_111, x_119);
lean_inc(x_143);
lean_inc(x_111);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_111);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_unsigned_to_nat(117u);
x_146 = l_Char_ofNat(x_145);
x_147 = l_instDecidableEqChar(x_142, x_146);
if (x_147 == 0)
{
if (x_139 == 0)
{
x_120 = x_143;
x_121 = x_144;
goto block_137;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_143);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_111);
x_148 = lean_mk_string_unchecked("", 0, 0);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
else
{
x_120 = x_143;
x_121 = x_144;
goto block_137;
}
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("", 0, 0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
block_13:
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_uint32_add(x_8, x_7);
x_11 = lean_box_uint32(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_110:
{
lean_object* x_15; 
x_15 = l_Lean_Json_Parser_hexChar(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Json_Parser_hexChar(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Json_Parser_hexChar(x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint16_t x_26; uint16_t x_27; uint16_t x_28; lean_object* x_29; uint16_t x_30; uint16_t x_31; uint16_t x_32; uint16_t x_33; uint16_t x_34; uint16_t x_35; lean_object* x_36; uint16_t x_37; uint8_t x_38; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_unsigned_to_nat(8u);
x_26 = lean_uint16_of_nat(x_25);
x_27 = lean_unbox(x_17);
lean_dec(x_17);
x_28 = lean_uint16_shift_left(x_27, x_26);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_uint16_of_nat(x_29);
x_31 = lean_unbox(x_20);
lean_dec(x_20);
x_32 = lean_uint16_shift_left(x_31, x_30);
x_33 = lean_uint16_lor(x_28, x_32);
x_34 = lean_unbox(x_24);
lean_dec(x_24);
x_35 = lean_uint16_lor(x_33, x_34);
x_36 = lean_unsigned_to_nat(3072u);
x_37 = lean_uint16_of_nat(x_36);
x_38 = lean_uint16_dec_lt(x_35, x_37);
if (x_38 == 0)
{
uint32_t x_39; lean_object* x_40; uint32_t x_41; uint32_t x_42; lean_object* x_43; uint32_t x_44; uint32_t x_45; uint32_t x_46; uint32_t x_47; uint32_t x_48; lean_object* x_49; uint32_t x_50; uint32_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_21);
x_39 = lean_uint16_to_uint32(x_1);
x_40 = lean_unsigned_to_nat(1023u);
x_41 = lean_uint32_of_nat(x_40);
x_42 = lean_uint32_land(x_39, x_41);
x_43 = lean_unsigned_to_nat(10u);
x_44 = lean_uint32_of_nat(x_43);
x_45 = lean_uint32_shift_left(x_42, x_44);
x_46 = lean_uint16_to_uint32(x_35);
x_47 = lean_uint32_land(x_46, x_41);
x_48 = lean_uint32_lor(x_45, x_47);
x_49 = lean_unsigned_to_nat(65536u);
x_50 = lean_uint32_of_nat(x_49);
x_51 = lean_uint32_add(x_48, x_50);
x_52 = lean_uint32_to_nat(x_51);
x_53 = lean_unsigned_to_nat(55296u);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(57343u);
x_56 = lean_nat_dec_lt(x_55, x_52);
if (x_56 == 0)
{
lean_dec(x_52);
x_3 = x_23;
goto block_6;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_unsigned_to_nat(1114112u);
x_58 = lean_nat_dec_lt(x_52, x_57);
lean_dec(x_52);
if (x_58 == 0)
{
x_3 = x_23;
goto block_6;
}
else
{
x_7 = x_50;
x_8 = x_48;
x_9 = x_23;
goto block_13;
}
}
}
else
{
lean_dec(x_52);
x_7 = x_50;
x_8 = x_48;
x_9 = x_23;
goto block_13;
}
}
else
{
lean_object* x_59; 
x_59 = lean_mk_string_unchecked("", 0, 0);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_59);
return x_21;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint16_t x_63; uint16_t x_64; uint16_t x_65; lean_object* x_66; uint16_t x_67; uint16_t x_68; uint16_t x_69; uint16_t x_70; uint16_t x_71; uint16_t x_72; lean_object* x_73; uint16_t x_74; uint8_t x_75; 
x_60 = lean_ctor_get(x_21, 0);
x_61 = lean_ctor_get(x_21, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_21);
x_62 = lean_unsigned_to_nat(8u);
x_63 = lean_uint16_of_nat(x_62);
x_64 = lean_unbox(x_17);
lean_dec(x_17);
x_65 = lean_uint16_shift_left(x_64, x_63);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_uint16_of_nat(x_66);
x_68 = lean_unbox(x_20);
lean_dec(x_20);
x_69 = lean_uint16_shift_left(x_68, x_67);
x_70 = lean_uint16_lor(x_65, x_69);
x_71 = lean_unbox(x_61);
lean_dec(x_61);
x_72 = lean_uint16_lor(x_70, x_71);
x_73 = lean_unsigned_to_nat(3072u);
x_74 = lean_uint16_of_nat(x_73);
x_75 = lean_uint16_dec_lt(x_72, x_74);
if (x_75 == 0)
{
uint32_t x_76; lean_object* x_77; uint32_t x_78; uint32_t x_79; lean_object* x_80; uint32_t x_81; uint32_t x_82; uint32_t x_83; uint32_t x_84; uint32_t x_85; lean_object* x_86; uint32_t x_87; uint32_t x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_76 = lean_uint16_to_uint32(x_1);
x_77 = lean_unsigned_to_nat(1023u);
x_78 = lean_uint32_of_nat(x_77);
x_79 = lean_uint32_land(x_76, x_78);
x_80 = lean_unsigned_to_nat(10u);
x_81 = lean_uint32_of_nat(x_80);
x_82 = lean_uint32_shift_left(x_79, x_81);
x_83 = lean_uint16_to_uint32(x_72);
x_84 = lean_uint32_land(x_83, x_78);
x_85 = lean_uint32_lor(x_82, x_84);
x_86 = lean_unsigned_to_nat(65536u);
x_87 = lean_uint32_of_nat(x_86);
x_88 = lean_uint32_add(x_85, x_87);
x_89 = lean_uint32_to_nat(x_88);
x_90 = lean_unsigned_to_nat(55296u);
x_91 = lean_nat_dec_lt(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_unsigned_to_nat(57343u);
x_93 = lean_nat_dec_lt(x_92, x_89);
if (x_93 == 0)
{
lean_dec(x_89);
x_3 = x_60;
goto block_6;
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_unsigned_to_nat(1114112u);
x_95 = lean_nat_dec_lt(x_89, x_94);
lean_dec(x_89);
if (x_95 == 0)
{
x_3 = x_60;
goto block_6;
}
else
{
x_7 = x_87;
x_8 = x_85;
x_9 = x_60;
goto block_13;
}
}
}
else
{
lean_dec(x_89);
x_7 = x_87;
x_8 = x_85;
x_9 = x_60;
goto block_13;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_mk_string_unchecked("", 0, 0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_60);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_20);
lean_dec(x_17);
x_98 = !lean_is_exclusive(x_21);
if (x_98 == 0)
{
return x_21;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_21, 0);
x_100 = lean_ctor_get(x_21, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_21);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_17);
x_102 = !lean_is_exclusive(x_18);
if (x_102 == 0)
{
return x_18;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_18, 0);
x_104 = lean_ctor_get(x_18, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_18);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_15);
if (x_106 == 0)
{
return x_15;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_15, 0);
x_108 = lean_ctor_get(x_15, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_15);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_finishSurrogatePair___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Json_Parser_finishSurrogatePair(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_escapedChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_string_utf8_get_fast(x_2, x_3);
x_12 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_12);
x_13 = lean_unsigned_to_nat(92u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(34u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_11, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(47u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_instDecidableEqChar(x_11, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(98u);
x_23 = l_Char_ofNat(x_22);
x_24 = l_instDecidableEqChar(x_11, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(102u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_11, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(110u);
x_29 = l_Char_ofNat(x_28);
x_30 = l_instDecidableEqChar(x_11, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(114u);
x_32 = l_Char_ofNat(x_31);
x_33 = l_instDecidableEqChar(x_11, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_34 = lean_unsigned_to_nat(116u);
x_35 = l_Char_ofNat(x_34);
x_36 = l_instDecidableEqChar(x_11, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint32_t x_38; uint8_t x_39; 
x_37 = lean_unsigned_to_nat(117u);
x_38 = l_Char_ofNat(x_37);
x_39 = l_instDecidableEqChar(x_11, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_mk_string_unchecked("illegal \\u escape", 17, 17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Json_Parser_hexChar(x_1);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Json_Parser_hexChar(x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Json_Parser_hexChar(x_46);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = l_Lean_Json_Parser_hexChar(x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_66; uint16_t x_67; uint16_t x_68; uint16_t x_69; lean_object* x_70; uint16_t x_71; uint16_t x_72; uint16_t x_73; uint16_t x_74; lean_object* x_75; uint16_t x_76; uint16_t x_77; uint16_t x_78; uint16_t x_79; uint16_t x_80; uint16_t x_81; lean_object* x_82; uint16_t x_83; uint8_t x_84; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_66 = lean_unsigned_to_nat(12u);
x_67 = lean_uint16_of_nat(x_66);
x_68 = lean_unbox(x_44);
lean_dec(x_44);
x_69 = lean_uint16_shift_left(x_68, x_67);
x_70 = lean_unsigned_to_nat(8u);
x_71 = lean_uint16_of_nat(x_70);
x_72 = lean_unbox(x_47);
lean_dec(x_47);
x_73 = lean_uint16_shift_left(x_72, x_71);
x_74 = lean_uint16_lor(x_69, x_73);
x_75 = lean_unsigned_to_nat(4u);
x_76 = lean_uint16_of_nat(x_75);
x_77 = lean_unbox(x_51);
lean_dec(x_51);
x_78 = lean_uint16_shift_left(x_77, x_76);
x_79 = lean_uint16_lor(x_74, x_78);
x_80 = lean_unbox(x_54);
lean_dec(x_54);
x_81 = lean_uint16_lor(x_79, x_80);
x_82 = lean_unsigned_to_nat(55296u);
x_83 = lean_uint16_of_nat(x_82);
x_84 = lean_uint16_dec_lt(x_81, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint16_t x_86; uint8_t x_87; 
x_85 = lean_unsigned_to_nat(57344u);
x_86 = lean_uint16_of_nat(x_85);
x_87 = lean_uint16_dec_lt(x_81, x_86);
if (x_87 == 0)
{
uint32_t x_88; lean_object* x_89; 
lean_dec(x_55);
x_88 = lean_uint16_to_uint32(x_81);
x_89 = lean_box_uint32(x_88);
lean_ctor_set(x_48, 1, x_89);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
else
{
lean_object* x_90; uint16_t x_91; uint8_t x_92; 
x_90 = lean_unsigned_to_nat(56320u);
x_91 = lean_uint16_of_nat(x_90);
x_92 = lean_uint16_dec_lt(x_81, x_91);
if (x_92 == 0)
{
lean_object* x_93; uint32_t x_94; lean_object* x_95; 
lean_dec(x_55);
x_93 = lean_unsigned_to_nat(65533u);
x_94 = l_Char_ofNat(x_93);
x_95 = lean_box_uint32(x_94);
lean_ctor_set(x_48, 1, x_95);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
else
{
lean_object* x_96; 
lean_free_object(x_48);
lean_inc(x_53);
x_96 = l_Lean_Json_Parser_finishSurrogatePair(x_81, x_53);
if (lean_obj_tag(x_96) == 0)
{
if (lean_obj_tag(x_96) == 0)
{
lean_dec(x_55);
lean_dec(x_53);
return x_96;
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_56 = x_96;
x_57 = x_97;
goto block_65;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
lean_inc(x_53);
lean_ctor_set(x_96, 0, x_53);
lean_inc(x_53);
x_56 = x_96;
x_57 = x_53;
goto block_65;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
lean_inc(x_53);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_53);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_53);
x_56 = x_101;
x_57 = x_53;
goto block_65;
}
}
}
}
}
else
{
uint32_t x_102; lean_object* x_103; 
lean_dec(x_55);
x_102 = lean_uint16_to_uint32(x_81);
x_103 = lean_box_uint32(x_102);
lean_ctor_set(x_48, 1, x_103);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
block_65:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = l_instDecidableEqPos(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_dec(x_57);
lean_dec(x_55);
return x_56;
}
else
{
lean_object* x_61; uint32_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_56);
x_61 = lean_unsigned_to_nat(65533u);
x_62 = l_Char_ofNat(x_61);
x_63 = lean_box_uint32(x_62);
if (lean_is_scalar(x_55)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_55;
}
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_104; 
lean_free_object(x_48);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_44);
x_104 = !lean_is_exclusive(x_52);
if (x_104 == 0)
{
return x_52;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_52, 0);
x_106 = lean_ctor_get(x_52, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_52);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_48, 0);
x_109 = lean_ctor_get(x_48, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_48);
x_110 = l_Lean_Json_Parser_hexChar(x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_124; uint16_t x_125; uint16_t x_126; uint16_t x_127; lean_object* x_128; uint16_t x_129; uint16_t x_130; uint16_t x_131; uint16_t x_132; lean_object* x_133; uint16_t x_134; uint16_t x_135; uint16_t x_136; uint16_t x_137; uint16_t x_138; uint16_t x_139; lean_object* x_140; uint16_t x_141; uint8_t x_142; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_124 = lean_unsigned_to_nat(12u);
x_125 = lean_uint16_of_nat(x_124);
x_126 = lean_unbox(x_44);
lean_dec(x_44);
x_127 = lean_uint16_shift_left(x_126, x_125);
x_128 = lean_unsigned_to_nat(8u);
x_129 = lean_uint16_of_nat(x_128);
x_130 = lean_unbox(x_47);
lean_dec(x_47);
x_131 = lean_uint16_shift_left(x_130, x_129);
x_132 = lean_uint16_lor(x_127, x_131);
x_133 = lean_unsigned_to_nat(4u);
x_134 = lean_uint16_of_nat(x_133);
x_135 = lean_unbox(x_109);
lean_dec(x_109);
x_136 = lean_uint16_shift_left(x_135, x_134);
x_137 = lean_uint16_lor(x_132, x_136);
x_138 = lean_unbox(x_112);
lean_dec(x_112);
x_139 = lean_uint16_lor(x_137, x_138);
x_140 = lean_unsigned_to_nat(55296u);
x_141 = lean_uint16_of_nat(x_140);
x_142 = lean_uint16_dec_lt(x_139, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint16_t x_144; uint8_t x_145; 
x_143 = lean_unsigned_to_nat(57344u);
x_144 = lean_uint16_of_nat(x_143);
x_145 = lean_uint16_dec_lt(x_139, x_144);
if (x_145 == 0)
{
uint32_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_113);
x_146 = lean_uint16_to_uint32(x_139);
x_147 = lean_box_uint32(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_111);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
else
{
lean_object* x_149; uint16_t x_150; uint8_t x_151; 
x_149 = lean_unsigned_to_nat(56320u);
x_150 = lean_uint16_of_nat(x_149);
x_151 = lean_uint16_dec_lt(x_139, x_150);
if (x_151 == 0)
{
lean_object* x_152; uint32_t x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_113);
x_152 = lean_unsigned_to_nat(65533u);
x_153 = l_Char_ofNat(x_152);
x_154 = lean_box_uint32(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_111);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
else
{
lean_object* x_156; 
lean_inc(x_111);
x_156 = l_Lean_Json_Parser_finishSurrogatePair(x_139, x_111);
if (lean_obj_tag(x_156) == 0)
{
if (lean_obj_tag(x_156) == 0)
{
lean_dec(x_113);
lean_dec(x_111);
return x_156;
}
else
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_114 = x_156;
x_115 = x_157;
goto block_123;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
lean_inc(x_111);
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_111);
lean_ctor_set(x_160, 1, x_158);
lean_inc(x_111);
x_114 = x_160;
x_115 = x_111;
goto block_123;
}
}
}
}
else
{
uint32_t x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_113);
x_161 = lean_uint16_to_uint32(x_139);
x_162 = lean_box_uint32(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_111);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
block_123:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
x_118 = l_instDecidableEqPos(x_116, x_117);
lean_dec(x_117);
lean_dec(x_116);
if (x_118 == 0)
{
lean_dec(x_115);
lean_dec(x_113);
return x_114;
}
else
{
lean_object* x_119; uint32_t x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_114);
x_119 = lean_unsigned_to_nat(65533u);
x_120 = l_Char_ofNat(x_119);
x_121 = lean_box_uint32(x_120);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_115);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_109);
lean_dec(x_47);
lean_dec(x_44);
x_164 = lean_ctor_get(x_110, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_110, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_166 = x_110;
} else {
 lean_dec_ref(x_110);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_47);
lean_dec(x_44);
x_168 = !lean_is_exclusive(x_48);
if (x_168 == 0)
{
return x_48;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_48, 0);
x_170 = lean_ctor_get(x_48, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_48);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_44);
x_172 = !lean_is_exclusive(x_45);
if (x_172 == 0)
{
return x_45;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_45, 0);
x_174 = lean_ctor_get(x_45, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_45);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_42);
if (x_176 == 0)
{
return x_42;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_42, 0);
x_178 = lean_ctor_get(x_42, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_42);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
else
{
lean_object* x_180; uint32_t x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_unsigned_to_nat(9u);
x_181 = l_Char_ofNat(x_180);
x_182 = lean_box_uint32(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
else
{
lean_object* x_184; uint32_t x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_unsigned_to_nat(13u);
x_185 = l_Char_ofNat(x_184);
x_186 = lean_box_uint32(x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_1);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
else
{
lean_object* x_188; uint32_t x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_unsigned_to_nat(10u);
x_189 = l_Char_ofNat(x_188);
x_190 = lean_box_uint32(x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_1);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
else
{
lean_object* x_192; uint32_t x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_unsigned_to_nat(12u);
x_193 = l_Char_ofNat(x_192);
x_194 = lean_box_uint32(x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_1);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
else
{
lean_object* x_196; uint32_t x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_unsigned_to_nat(8u);
x_197 = l_Char_ofNat(x_196);
x_198 = lean_box_uint32(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_1);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_box_uint32(x_20);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_1);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_box_uint32(x_17);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_box_uint32(x_14);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_1);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
else
{
uint32_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint32_t x_210; uint8_t x_211; 
lean_dec(x_1);
x_206 = lean_string_utf8_get_fast(x_2, x_3);
x_207 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_2);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_unsigned_to_nat(92u);
x_210 = l_Char_ofNat(x_209);
x_211 = l_instDecidableEqChar(x_206, x_210);
if (x_211 == 0)
{
lean_object* x_212; uint32_t x_213; uint8_t x_214; 
x_212 = lean_unsigned_to_nat(34u);
x_213 = l_Char_ofNat(x_212);
x_214 = l_instDecidableEqChar(x_206, x_213);
if (x_214 == 0)
{
lean_object* x_215; uint32_t x_216; uint8_t x_217; 
x_215 = lean_unsigned_to_nat(47u);
x_216 = l_Char_ofNat(x_215);
x_217 = l_instDecidableEqChar(x_206, x_216);
if (x_217 == 0)
{
lean_object* x_218; uint32_t x_219; uint8_t x_220; 
x_218 = lean_unsigned_to_nat(98u);
x_219 = l_Char_ofNat(x_218);
x_220 = l_instDecidableEqChar(x_206, x_219);
if (x_220 == 0)
{
lean_object* x_221; uint32_t x_222; uint8_t x_223; 
x_221 = lean_unsigned_to_nat(102u);
x_222 = l_Char_ofNat(x_221);
x_223 = l_instDecidableEqChar(x_206, x_222);
if (x_223 == 0)
{
lean_object* x_224; uint32_t x_225; uint8_t x_226; 
x_224 = lean_unsigned_to_nat(110u);
x_225 = l_Char_ofNat(x_224);
x_226 = l_instDecidableEqChar(x_206, x_225);
if (x_226 == 0)
{
lean_object* x_227; uint32_t x_228; uint8_t x_229; 
x_227 = lean_unsigned_to_nat(114u);
x_228 = l_Char_ofNat(x_227);
x_229 = l_instDecidableEqChar(x_206, x_228);
if (x_229 == 0)
{
lean_object* x_230; uint32_t x_231; uint8_t x_232; 
x_230 = lean_unsigned_to_nat(116u);
x_231 = l_Char_ofNat(x_230);
x_232 = l_instDecidableEqChar(x_206, x_231);
if (x_232 == 0)
{
lean_object* x_233; uint32_t x_234; uint8_t x_235; 
x_233 = lean_unsigned_to_nat(117u);
x_234 = l_Char_ofNat(x_233);
x_235 = l_instDecidableEqChar(x_206, x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_mk_string_unchecked("illegal \\u escape", 17, 17);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_208);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
else
{
lean_object* x_238; 
x_238 = l_Lean_Json_Parser_hexChar(x_208);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Json_Parser_hexChar(x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Json_Parser_hexChar(x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = l_Lean_Json_Parser_hexChar(x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_262; uint16_t x_263; uint16_t x_264; uint16_t x_265; lean_object* x_266; uint16_t x_267; uint16_t x_268; uint16_t x_269; uint16_t x_270; lean_object* x_271; uint16_t x_272; uint16_t x_273; uint16_t x_274; uint16_t x_275; uint16_t x_276; uint16_t x_277; lean_object* x_278; uint16_t x_279; uint8_t x_280; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_251 = x_248;
} else {
 lean_dec_ref(x_248);
 x_251 = lean_box(0);
}
x_262 = lean_unsigned_to_nat(12u);
x_263 = lean_uint16_of_nat(x_262);
x_264 = lean_unbox(x_240);
lean_dec(x_240);
x_265 = lean_uint16_shift_left(x_264, x_263);
x_266 = lean_unsigned_to_nat(8u);
x_267 = lean_uint16_of_nat(x_266);
x_268 = lean_unbox(x_243);
lean_dec(x_243);
x_269 = lean_uint16_shift_left(x_268, x_267);
x_270 = lean_uint16_lor(x_265, x_269);
x_271 = lean_unsigned_to_nat(4u);
x_272 = lean_uint16_of_nat(x_271);
x_273 = lean_unbox(x_246);
lean_dec(x_246);
x_274 = lean_uint16_shift_left(x_273, x_272);
x_275 = lean_uint16_lor(x_270, x_274);
x_276 = lean_unbox(x_250);
lean_dec(x_250);
x_277 = lean_uint16_lor(x_275, x_276);
x_278 = lean_unsigned_to_nat(55296u);
x_279 = lean_uint16_of_nat(x_278);
x_280 = lean_uint16_dec_lt(x_277, x_279);
if (x_280 == 0)
{
lean_object* x_281; uint16_t x_282; uint8_t x_283; 
x_281 = lean_unsigned_to_nat(57344u);
x_282 = lean_uint16_of_nat(x_281);
x_283 = lean_uint16_dec_lt(x_277, x_282);
if (x_283 == 0)
{
uint32_t x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_251);
x_284 = lean_uint16_to_uint32(x_277);
x_285 = lean_box_uint32(x_284);
if (lean_is_scalar(x_247)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_247;
}
lean_ctor_set(x_286, 0, x_249);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
else
{
lean_object* x_287; uint16_t x_288; uint8_t x_289; 
x_287 = lean_unsigned_to_nat(56320u);
x_288 = lean_uint16_of_nat(x_287);
x_289 = lean_uint16_dec_lt(x_277, x_288);
if (x_289 == 0)
{
lean_object* x_290; uint32_t x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_251);
x_290 = lean_unsigned_to_nat(65533u);
x_291 = l_Char_ofNat(x_290);
x_292 = lean_box_uint32(x_291);
if (lean_is_scalar(x_247)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_247;
}
lean_ctor_set(x_293, 0, x_249);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
else
{
lean_object* x_294; 
lean_dec(x_247);
lean_inc(x_249);
x_294 = l_Lean_Json_Parser_finishSurrogatePair(x_277, x_249);
if (lean_obj_tag(x_294) == 0)
{
if (lean_obj_tag(x_294) == 0)
{
lean_dec(x_251);
lean_dec(x_249);
return x_294;
}
else
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_252 = x_294;
x_253 = x_295;
goto block_261;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_297 = x_294;
} else {
 lean_dec_ref(x_294);
 x_297 = lean_box(0);
}
lean_inc(x_249);
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_249);
lean_ctor_set(x_298, 1, x_296);
lean_inc(x_249);
x_252 = x_298;
x_253 = x_249;
goto block_261;
}
}
}
}
else
{
uint32_t x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_251);
x_299 = lean_uint16_to_uint32(x_277);
x_300 = lean_box_uint32(x_299);
if (lean_is_scalar(x_247)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_247;
}
lean_ctor_set(x_301, 0, x_249);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
block_261:
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_dec(x_249);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
x_256 = l_instDecidableEqPos(x_254, x_255);
lean_dec(x_255);
lean_dec(x_254);
if (x_256 == 0)
{
lean_dec(x_253);
lean_dec(x_251);
return x_252;
}
else
{
lean_object* x_257; uint32_t x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_252);
x_257 = lean_unsigned_to_nat(65533u);
x_258 = l_Char_ofNat(x_257);
x_259 = lean_box_uint32(x_258);
if (lean_is_scalar(x_251)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_251;
}
lean_ctor_set(x_260, 0, x_253);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_243);
lean_dec(x_240);
x_302 = lean_ctor_get(x_248, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_248, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_304 = x_248;
} else {
 lean_dec_ref(x_248);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_243);
lean_dec(x_240);
x_306 = lean_ctor_get(x_244, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_244, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_308 = x_244;
} else {
 lean_dec_ref(x_244);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_240);
x_310 = lean_ctor_get(x_241, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_241, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_312 = x_241;
} else {
 lean_dec_ref(x_241);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_238, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_238, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_316 = x_238;
} else {
 lean_dec_ref(x_238);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
else
{
lean_object* x_318; uint32_t x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_unsigned_to_nat(9u);
x_319 = l_Char_ofNat(x_318);
x_320 = lean_box_uint32(x_319);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_208);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
else
{
lean_object* x_322; uint32_t x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_unsigned_to_nat(13u);
x_323 = l_Char_ofNat(x_322);
x_324 = lean_box_uint32(x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_208);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
else
{
lean_object* x_326; uint32_t x_327; lean_object* x_328; lean_object* x_329; 
x_326 = lean_unsigned_to_nat(10u);
x_327 = l_Char_ofNat(x_326);
x_328 = lean_box_uint32(x_327);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_208);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
else
{
lean_object* x_330; uint32_t x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_unsigned_to_nat(12u);
x_331 = l_Char_ofNat(x_330);
x_332 = lean_box_uint32(x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_208);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
else
{
lean_object* x_334; uint32_t x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_unsigned_to_nat(8u);
x_335 = l_Char_ofNat(x_334);
x_336 = lean_box_uint32(x_335);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_208);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_box_uint32(x_216);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_208);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_box_uint32(x_213);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_208);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_box_uint32(x_210);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_208);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_strCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_unsigned_to_nat(34u);
x_11 = l_Char_ofNat(x_10);
x_12 = l_instDecidableEqChar(x_9, x_11);
if (x_12 == 0)
{
if (x_6 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
x_18 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_18);
x_25 = lean_unsigned_to_nat(92u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_9, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint32_of_nat(x_28);
x_30 = lean_uint32_dec_le(x_29, x_9);
if (x_30 == 0)
{
x_19 = x_30;
goto block_24;
}
else
{
lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(1114111u);
x_32 = lean_uint32_of_nat(x_31);
x_33 = lean_uint32_dec_le(x_9, x_32);
x_19 = x_33;
goto block_24;
}
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Json_Parser_escapedChar(x_2);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint32_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox_uint32(x_36);
lean_dec(x_36);
x_38 = lean_string_push(x_1, x_37);
x_1 = x_38;
x_2 = x_35;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
block_24:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("unexpected character in string", 30, 30);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_string_push(x_1, x_9);
x_1 = x_22;
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_52; uint32_t x_53; uint8_t x_54; 
lean_dec(x_2);
x_44 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_44);
x_52 = lean_unsigned_to_nat(92u);
x_53 = l_Char_ofNat(x_52);
x_54 = l_instDecidableEqChar(x_9, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint32_t x_56; uint8_t x_57; 
x_55 = lean_unsigned_to_nat(32u);
x_56 = lean_uint32_of_nat(x_55);
x_57 = lean_uint32_dec_le(x_56, x_9);
if (x_57 == 0)
{
x_46 = x_57;
goto block_51;
}
else
{
lean_object* x_58; uint32_t x_59; uint8_t x_60; 
x_58 = lean_unsigned_to_nat(1114111u);
x_59 = lean_uint32_of_nat(x_58);
x_60 = lean_uint32_dec_le(x_9, x_59);
x_46 = x_60;
goto block_51;
}
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Json_Parser_escapedChar(x_45);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint32_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unbox_uint32(x_63);
lean_dec(x_63);
x_65 = lean_string_push(x_1, x_64);
x_1 = x_65;
x_2 = x_62;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
block_51:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = lean_mk_string_unchecked("unexpected character in string", 30, 30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_string_push(x_1, x_9);
x_1 = x_49;
x_2 = x_45;
goto _start;
}
}
}
}
}
else
{
if (x_6 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_2);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_2, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_2, 0);
lean_dec(x_75);
x_76 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_1);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_78 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_3);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_1);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_str(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = l_Lean_Json_Parser_strCore(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
else
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; lean_object* x_11; uint8_t x_12; uint32_t x_37; uint8_t x_38; 
x_10 = lean_string_utf8_get_fast(x_3, x_4);
x_11 = lean_unsigned_to_nat(48u);
x_37 = l_Char_ofNat(x_11);
x_38 = lean_uint32_dec_le(x_37, x_10);
if (x_38 == 0)
{
x_12 = x_38;
goto block_36;
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(57u);
x_40 = l_Char_ofNat(x_39);
x_41 = lean_uint32_dec_le(x_10, x_40);
x_12 = x_41;
goto block_36;
}
block_36:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
return x_13;
}
else
{
if (x_6 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; uint32_t x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 0);
lean_dec(x_18);
x_19 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_19);
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_mul(x_20, x_1);
lean_dec(x_1);
x_22 = l_Char_ofNat(x_11);
x_23 = lean_uint32_sub(x_10, x_22);
x_24 = lean_uint32_to_nat(x_23);
x_25 = lean_nat_add(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
x_1 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint32_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_27 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(10u);
x_30 = lean_nat_mul(x_29, x_1);
lean_dec(x_1);
x_31 = l_Char_ofNat(x_11);
x_32 = lean_uint32_sub(x_10, x_31);
x_33 = lean_uint32_to_nat(x_32);
x_34 = lean_nat_add(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
x_1 = x_34;
x_2 = x_28;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natCoreNumDigits(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
if (x_7 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint32_t x_12; lean_object* x_13; uint8_t x_14; uint32_t x_44; uint8_t x_45; 
x_12 = lean_string_utf8_get_fast(x_4, x_5);
x_13 = lean_unsigned_to_nat(48u);
x_44 = l_Char_ofNat(x_13);
x_45 = lean_uint32_dec_le(x_44, x_12);
if (x_45 == 0)
{
x_14 = x_45;
goto block_43;
}
else
{
lean_object* x_46; uint32_t x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(57u);
x_47 = l_Char_ofNat(x_46);
x_48 = lean_uint32_dec_le(x_12, x_47);
x_14 = x_48;
goto block_43;
}
block_43:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
if (x_7 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_3, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_3, 0);
lean_dec(x_21);
x_22 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_22);
x_23 = lean_unsigned_to_nat(10u);
x_24 = lean_nat_mul(x_23, x_1);
lean_dec(x_1);
x_25 = l_Char_ofNat(x_13);
x_26 = lean_uint32_sub(x_12, x_25);
x_27 = lean_uint32_to_nat(x_26);
x_28 = lean_nat_add(x_24, x_27);
lean_dec(x_27);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint32_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_32 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(10u);
x_35 = lean_nat_mul(x_34, x_1);
lean_dec(x_1);
x_36 = l_Char_ofNat(x_13);
x_37 = lean_uint32_sub(x_12, x_36);
x_38 = lean_uint32_to_nat(x_37);
x_39 = lean_nat_add(x_35, x_38);
lean_dec(x_38);
lean_dec(x_35);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_2, x_40);
lean_dec(x_2);
x_1 = x_39;
x_2 = x_41;
x_3 = x_33;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_string_utf8_get_fast(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_box_uint32(x_10);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_mk_string_unchecked("expected ", 9, 9);
x_15 = lean_string_append(x_14, x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint32_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_string_utf8_get_fast(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_box_uint32(x_11);
x_13 = lean_apply_1(x_3, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_mk_string_unchecked("expected ", 9, 9);
x_16 = lean_string_append(x_15, x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_Parser_lookahead___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_lookahead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_Parser_lookahead(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNonZero(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_unsigned_to_nat(49u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_uint32_dec_le(x_16, x_14);
if (x_17 == 0)
{
x_2 = x_17;
goto block_7;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(57u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_dec_le(x_14, x_19);
x_2 = x_20;
goto block_7;
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("expected 1-9", 12, 12);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCore(x_5, x_1);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_unsigned_to_nat(48u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_uint32_dec_le(x_16, x_14);
if (x_17 == 0)
{
x_2 = x_17;
goto block_7;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(57u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_dec_le(x_14, x_19);
x_2 = x_20;
goto block_7;
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("expected digit", 14, 14);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCoreNumDigits(x_5, x_5, x_1);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_unsigned_to_nat(48u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_uint32_dec_le(x_16, x_14);
if (x_17 == 0)
{
x_2 = x_17;
goto block_7;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(57u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_dec_le(x_14, x_19);
x_2 = x_20;
goto block_7;
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("expected 0-9", 12, 12);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCore(x_5, x_1);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numSign(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = lean_unsigned_to_nat(45u);
x_10 = l_Char_ofNat(x_9);
x_11 = l_instDecidableEqChar(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
if (x_5 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_20);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_25 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_neg(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_nat(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_14 = lean_string_utf8_get_fast(x_8, x_9);
x_15 = lean_unsigned_to_nat(48u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_14, x_16);
if (x_17 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(49u);
x_21 = l_Char_ofNat(x_20);
x_22 = lean_uint32_dec_le(x_21, x_14);
if (x_22 == 0)
{
x_2 = x_22;
goto block_7;
}
else
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(57u);
x_24 = l_Char_ofNat(x_23);
x_25 = lean_uint32_dec_le(x_14, x_24);
x_2 = x_25;
goto block_7;
}
}
}
else
{
if (x_11 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_8);
x_26 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 0);
lean_dec(x_30);
x_31 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_34 = lean_string_utf8_next_fast(x_8, x_9);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
block_7:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("expected 1-9", 12, 12);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Json_Parser_natCore(x_5, x_1);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_numWithDecimals(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_1, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_1, 1);
lean_inc(x_149);
x_150 = lean_string_utf8_byte_size(x_148);
x_151 = lean_nat_dec_lt(x_149, x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_149);
lean_dec(x_148);
x_152 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
else
{
uint32_t x_154; lean_object* x_155; uint32_t x_156; uint8_t x_157; 
x_154 = lean_string_utf8_get_fast(x_148, x_149);
x_155 = lean_unsigned_to_nat(45u);
x_156 = l_Char_ofNat(x_155);
x_157 = l_instDecidableEqChar(x_154, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_to_int(x_158);
x_122 = x_1;
x_123 = x_148;
x_124 = x_149;
x_125 = x_159;
goto block_147;
}
else
{
if (x_151 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_149);
lean_dec(x_148);
x_160 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_1);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_1);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_1, 1);
lean_dec(x_163);
x_164 = lean_ctor_get(x_1, 0);
lean_dec(x_164);
x_165 = lean_string_utf8_next_fast(x_148, x_149);
lean_dec(x_149);
lean_inc(x_165);
lean_inc(x_148);
lean_ctor_set(x_1, 1, x_165);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_to_int(x_166);
x_168 = lean_int_neg(x_167);
lean_dec(x_167);
x_122 = x_1;
x_123 = x_148;
x_124 = x_165;
x_125 = x_168;
goto block_147;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_1);
x_169 = lean_string_utf8_next_fast(x_148, x_149);
lean_dec(x_149);
lean_inc(x_169);
lean_inc(x_148);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_148);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_to_int(x_171);
x_173 = lean_int_neg(x_172);
lean_dec(x_172);
x_122 = x_170;
x_123 = x_148;
x_124 = x_169;
x_125 = x_173;
goto block_147;
}
}
}
}
block_69:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("expected digit", 14, 14);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Json_Parser_natCoreNumDigits(x_8, x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_System_Platform_numBits;
x_17 = lean_nat_pow(x_15, x_16);
x_18 = lean_nat_dec_lt(x_17, x_14);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_nat_to_int(x_2);
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_pow(x_20, x_14);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_mul(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
x_24 = lean_nat_to_int(x_13);
x_25 = lean_int_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_int_mul(x_3, x_25);
lean_dec(x_25);
lean_dec(x_3);
lean_ctor_set(x_11, 0, x_26);
return x_9;
}
else
{
lean_object* x_27; 
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_mk_string_unchecked("too many decimals", 17, 17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_27);
return x_9;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_unsigned_to_nat(2u);
x_31 = l_System_Platform_numBits;
x_32 = lean_nat_pow(x_30, x_31);
x_33 = lean_nat_dec_lt(x_32, x_29);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_nat_to_int(x_2);
x_35 = lean_unsigned_to_nat(10u);
x_36 = lean_nat_pow(x_35, x_29);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_int_mul(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
x_39 = lean_nat_to_int(x_28);
x_40 = lean_int_add(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
x_41 = lean_int_mul(x_3, x_40);
lean_dec(x_40);
lean_dec(x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_9, 1, x_42);
return x_9;
}
else
{
lean_object* x_43; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_mk_string_unchecked("too many decimals", 17, 17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_43);
return x_9;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_ctor_get(x_9, 1);
x_45 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
lean_inc(x_45);
lean_dec(x_9);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_System_Platform_numBits;
x_51 = lean_nat_pow(x_49, x_50);
x_52 = lean_nat_dec_lt(x_51, x_47);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_nat_to_int(x_2);
x_54 = lean_unsigned_to_nat(10u);
x_55 = lean_nat_pow(x_54, x_47);
x_56 = lean_nat_to_int(x_55);
x_57 = lean_int_mul(x_53, x_56);
lean_dec(x_56);
lean_dec(x_53);
x_58 = lean_nat_to_int(x_46);
x_59 = lean_int_add(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
x_60 = lean_int_mul(x_3, x_59);
lean_dec(x_59);
lean_dec(x_3);
if (lean_is_scalar(x_48)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_48;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_47);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_mk_string_unchecked("too many decimals", 17, 17);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
return x_9;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
block_105:
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_string_utf8_byte_size(x_72);
x_76 = lean_nat_dec_lt(x_73, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
x_77 = lean_nat_to_int(x_74);
x_78 = lean_int_mul(x_70, x_77);
lean_dec(x_77);
lean_dec(x_70);
x_79 = l_Lean_JsonNumber_fromInt(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
if (x_76 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_70);
x_81 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
uint32_t x_83; lean_object* x_84; uint32_t x_85; uint8_t x_86; 
x_83 = lean_string_utf8_get_fast(x_72, x_73);
x_84 = lean_unsigned_to_nat(46u);
x_85 = l_Char_ofNat(x_84);
x_86 = l_instDecidableEqChar(x_83, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
x_87 = lean_nat_to_int(x_74);
x_88 = lean_int_mul(x_70, x_87);
lean_dec(x_87);
lean_dec(x_70);
x_89 = l_Lean_JsonNumber_fromInt(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_71);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
if (x_76 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_70);
x_91 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_71);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_71);
x_93 = lean_string_utf8_next_fast(x_72, x_73);
lean_dec(x_73);
lean_inc(x_93);
lean_inc(x_72);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_72);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_nat_dec_lt(x_93, x_75);
lean_dec(x_75);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_70);
x_96 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
else
{
uint32_t x_98; lean_object* x_99; uint32_t x_100; uint8_t x_101; 
x_98 = lean_string_utf8_get_fast(x_72, x_93);
lean_dec(x_93);
lean_dec(x_72);
x_99 = lean_unsigned_to_nat(48u);
x_100 = l_Char_ofNat(x_99);
x_101 = lean_uint32_dec_le(x_100, x_98);
if (x_101 == 0)
{
x_2 = x_74;
x_3 = x_70;
x_4 = x_94;
x_5 = x_101;
goto block_69;
}
else
{
lean_object* x_102; uint32_t x_103; uint8_t x_104; 
x_102 = lean_unsigned_to_nat(57u);
x_103 = l_Char_ofNat(x_102);
x_104 = lean_uint32_dec_le(x_98, x_103);
x_2 = x_74;
x_3 = x_70;
x_4 = x_94;
x_5 = x_104;
goto block_69;
}
}
}
}
}
}
}
block_121:
{
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_107);
x_109 = lean_mk_string_unchecked("expected 1-9", 12, 12);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Lean_Json_Parser_natCore(x_111, x_106);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
x_70 = x_107;
x_71 = x_113;
x_72 = x_115;
x_73 = x_116;
x_74 = x_114;
goto block_105;
}
else
{
uint8_t x_117; 
lean_dec(x_107);
x_117 = !lean_is_exclusive(x_112);
if (x_117 == 0)
{
return x_112;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_112, 0);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_112);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
block_147:
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_string_utf8_byte_size(x_123);
x_127 = lean_nat_dec_lt(x_124, x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
x_128 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_122);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
else
{
uint32_t x_130; lean_object* x_131; uint32_t x_132; uint8_t x_133; 
x_130 = lean_string_utf8_get_fast(x_123, x_124);
x_131 = lean_unsigned_to_nat(48u);
x_132 = l_Char_ofNat(x_131);
x_133 = l_instDecidableEqChar(x_130, x_132);
if (x_133 == 0)
{
lean_dec(x_124);
lean_dec(x_123);
if (x_127 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
x_134 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_122);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
else
{
lean_object* x_136; uint32_t x_137; uint8_t x_138; 
x_136 = lean_unsigned_to_nat(49u);
x_137 = l_Char_ofNat(x_136);
x_138 = lean_uint32_dec_le(x_137, x_130);
if (x_138 == 0)
{
x_106 = x_122;
x_107 = x_125;
x_108 = x_138;
goto block_121;
}
else
{
lean_object* x_139; uint32_t x_140; uint8_t x_141; 
x_139 = lean_unsigned_to_nat(57u);
x_140 = l_Char_ofNat(x_139);
x_141 = lean_uint32_dec_le(x_130, x_140);
x_106 = x_122;
x_107 = x_125;
x_108 = x_141;
goto block_121;
}
}
}
else
{
if (x_127 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
x_142 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_122);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_122);
x_144 = lean_string_utf8_next_fast(x_123, x_124);
lean_dec(x_124);
lean_inc(x_144);
lean_inc(x_123);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_123);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_unsigned_to_nat(0u);
x_70 = x_125;
x_71 = x_145;
x_72 = x_123;
x_73 = x_144;
x_74 = x_146;
goto block_105;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_exponent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_21; uint8_t x_22; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_65; lean_object* x_66; lean_object* x_134; uint8_t x_135; 
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_134 = lean_string_utf8_byte_size(x_65);
x_135 = lean_nat_dec_lt(x_66, x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_66);
lean_dec(x_65);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_2);
lean_ctor_set(x_136, 1, x_1);
return x_136;
}
else
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_1);
x_137 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
else
{
uint32_t x_139; lean_object* x_140; uint32_t x_141; uint8_t x_142; 
x_139 = lean_string_utf8_get_fast(x_65, x_66);
x_140 = lean_unsigned_to_nat(101u);
x_141 = l_Char_ofNat(x_140);
x_142 = l_instDecidableEqChar(x_139, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint32_t x_144; uint8_t x_145; 
x_143 = lean_unsigned_to_nat(69u);
x_144 = l_Char_ofNat(x_143);
x_145 = l_instDecidableEqChar(x_139, x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_66);
lean_dec(x_65);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_2);
lean_ctor_set(x_146, 1, x_1);
return x_146;
}
else
{
goto block_133;
}
}
else
{
goto block_133;
}
}
}
block_20:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("expected 0-9", 12, 12);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Json_Parser_natCore(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = l_Lean_JsonNumber_shiftr(x_1, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_JsonNumber_shiftr(x_1, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
block_49:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_mk_string_unchecked("expected 0-9", 12, 12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Json_Parser_natCore(x_25, x_21);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_unsigned_to_nat(2u);
x_30 = l_System_Platform_numBits;
x_31 = lean_nat_pow(x_29, x_30);
x_32 = lean_nat_dec_lt(x_31, x_28);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_JsonNumber_shiftl(x_1, x_28);
lean_dec(x_28);
lean_ctor_set(x_26, 1, x_33);
return x_26;
}
else
{
lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_1);
x_34 = lean_mk_string_unchecked("exp too large", 13, 13);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_34);
return x_26;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_unsigned_to_nat(2u);
x_38 = l_System_Platform_numBits;
x_39 = lean_nat_pow(x_37, x_38);
x_40 = lean_nat_dec_lt(x_39, x_36);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_JsonNumber_shiftl(x_1, x_36);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_1);
x_43 = lean_mk_string_unchecked("exp too large", 13, 13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_26);
if (x_45 == 0)
{
return x_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_26, 0);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_26);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
block_64:
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_string_utf8_byte_size(x_51);
x_54 = lean_nat_dec_lt(x_52, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_1);
x_55 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
uint32_t x_57; lean_object* x_58; uint32_t x_59; uint8_t x_60; 
x_57 = lean_string_utf8_get_fast(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
x_58 = lean_unsigned_to_nat(48u);
x_59 = l_Char_ofNat(x_58);
x_60 = lean_uint32_dec_le(x_59, x_57);
if (x_60 == 0)
{
x_21 = x_50;
x_22 = x_60;
goto block_49;
}
else
{
lean_object* x_61; uint32_t x_62; uint8_t x_63; 
x_61 = lean_unsigned_to_nat(57u);
x_62 = l_Char_ofNat(x_61);
x_63 = lean_uint32_dec_le(x_57, x_62);
x_21 = x_50;
x_22 = x_63;
goto block_49;
}
}
}
block_133:
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_string_utf8_byte_size(x_65);
x_68 = lean_nat_dec_lt(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_1);
x_69 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_2, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_2, 0);
lean_dec(x_73);
x_74 = lean_string_utf8_next_fast(x_65, x_66);
lean_dec(x_66);
lean_inc(x_74);
lean_inc(x_65);
lean_ctor_set(x_2, 1, x_74);
x_75 = lean_nat_dec_lt(x_74, x_67);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_74);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_1);
x_76 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
uint32_t x_78; lean_object* x_79; uint32_t x_80; uint8_t x_81; 
x_78 = lean_string_utf8_get_fast(x_65, x_74);
x_79 = lean_unsigned_to_nat(45u);
x_80 = l_Char_ofNat(x_79);
x_81 = l_instDecidableEqChar(x_78, x_80);
if (x_81 == 0)
{
lean_object* x_82; uint32_t x_83; uint8_t x_84; 
lean_dec(x_67);
x_82 = lean_unsigned_to_nat(43u);
x_83 = l_Char_ofNat(x_82);
x_84 = l_instDecidableEqChar(x_78, x_83);
if (x_84 == 0)
{
x_50 = x_2;
x_51 = x_65;
x_52 = x_74;
goto block_64;
}
else
{
if (x_75 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_74);
lean_dec(x_65);
lean_dec(x_1);
x_85 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_2);
x_87 = lean_string_utf8_next_fast(x_65, x_74);
lean_dec(x_74);
lean_inc(x_87);
lean_inc(x_65);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_65);
lean_ctor_set(x_88, 1, x_87);
x_50 = x_88;
x_51 = x_65;
x_52 = x_87;
goto block_64;
}
}
}
else
{
if (x_75 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_74);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_1);
x_89 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_2);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_2);
x_91 = lean_string_utf8_next_fast(x_65, x_74);
lean_dec(x_74);
lean_inc(x_91);
lean_inc(x_65);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_65);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_nat_dec_lt(x_91, x_67);
lean_dec(x_67);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_91);
lean_dec(x_65);
lean_dec(x_1);
x_94 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
uint32_t x_96; lean_object* x_97; uint32_t x_98; uint8_t x_99; 
x_96 = lean_string_utf8_get_fast(x_65, x_91);
lean_dec(x_91);
lean_dec(x_65);
x_97 = lean_unsigned_to_nat(48u);
x_98 = l_Char_ofNat(x_97);
x_99 = lean_uint32_dec_le(x_98, x_96);
if (x_99 == 0)
{
x_3 = x_92;
x_4 = x_99;
goto block_20;
}
else
{
lean_object* x_100; uint32_t x_101; uint8_t x_102; 
x_100 = lean_unsigned_to_nat(57u);
x_101 = l_Char_ofNat(x_100);
x_102 = lean_uint32_dec_le(x_96, x_101);
x_3 = x_92;
x_4 = x_102;
goto block_20;
}
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_2);
x_103 = lean_string_utf8_next_fast(x_65, x_66);
lean_dec(x_66);
lean_inc(x_103);
lean_inc(x_65);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_65);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_nat_dec_lt(x_103, x_67);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_103);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_1);
x_106 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
else
{
uint32_t x_108; lean_object* x_109; uint32_t x_110; uint8_t x_111; 
x_108 = lean_string_utf8_get_fast(x_65, x_103);
x_109 = lean_unsigned_to_nat(45u);
x_110 = l_Char_ofNat(x_109);
x_111 = l_instDecidableEqChar(x_108, x_110);
if (x_111 == 0)
{
lean_object* x_112; uint32_t x_113; uint8_t x_114; 
lean_dec(x_67);
x_112 = lean_unsigned_to_nat(43u);
x_113 = l_Char_ofNat(x_112);
x_114 = l_instDecidableEqChar(x_108, x_113);
if (x_114 == 0)
{
x_50 = x_104;
x_51 = x_65;
x_52 = x_103;
goto block_64;
}
else
{
if (x_105 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
lean_dec(x_65);
lean_dec(x_1);
x_115 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_104);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_104);
x_117 = lean_string_utf8_next_fast(x_65, x_103);
lean_dec(x_103);
lean_inc(x_117);
lean_inc(x_65);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_65);
lean_ctor_set(x_118, 1, x_117);
x_50 = x_118;
x_51 = x_65;
x_52 = x_117;
goto block_64;
}
}
}
else
{
if (x_105 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_103);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_1);
x_119 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_104);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_104);
x_121 = lean_string_utf8_next_fast(x_65, x_103);
lean_dec(x_103);
lean_inc(x_121);
lean_inc(x_65);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_65);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_nat_dec_lt(x_121, x_67);
lean_dec(x_67);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_121);
lean_dec(x_65);
lean_dec(x_1);
x_124 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
uint32_t x_126; lean_object* x_127; uint32_t x_128; uint8_t x_129; 
x_126 = lean_string_utf8_get_fast(x_65, x_121);
lean_dec(x_121);
lean_dec(x_65);
x_127 = lean_unsigned_to_nat(48u);
x_128 = l_Char_ofNat(x_127);
x_129 = lean_uint32_dec_le(x_128, x_126);
if (x_129 == 0)
{
x_3 = x_122;
x_4 = x_129;
goto block_20;
}
else
{
lean_object* x_130; uint32_t x_131; uint8_t x_132; 
x_130 = lean_unsigned_to_nat(57u);
x_131 = l_Char_ofNat(x_130);
x_132 = lean_uint32_dec_le(x_126, x_131);
x_3 = x_122;
x_4 = x_132;
goto block_20;
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
LEAN_EXPORT lean_object* l_Lean_Json_Parser_num(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_106; lean_object* x_107; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = lean_ctor_get(x_1, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_1, 1);
lean_inc(x_270);
x_271 = lean_string_utf8_byte_size(x_269);
x_272 = lean_nat_dec_lt(x_270, x_271);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_270);
lean_dec(x_269);
x_273 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_1);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
else
{
uint32_t x_275; lean_object* x_276; uint32_t x_277; uint8_t x_278; 
x_275 = lean_string_utf8_get_fast(x_269, x_270);
x_276 = lean_unsigned_to_nat(45u);
x_277 = l_Char_ofNat(x_276);
x_278 = l_instDecidableEqChar(x_275, x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_unsigned_to_nat(1u);
x_280 = lean_nat_to_int(x_279);
x_243 = x_1;
x_244 = x_269;
x_245 = x_270;
x_246 = x_280;
goto block_268;
}
else
{
if (x_272 == 0)
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_270);
lean_dec(x_269);
x_281 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_1);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
else
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_1);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_284 = lean_ctor_get(x_1, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_1, 0);
lean_dec(x_285);
x_286 = lean_string_utf8_next_fast(x_269, x_270);
lean_dec(x_270);
lean_inc(x_286);
lean_inc(x_269);
lean_ctor_set(x_1, 1, x_286);
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_nat_to_int(x_287);
x_289 = lean_int_neg(x_288);
lean_dec(x_288);
x_243 = x_1;
x_244 = x_269;
x_245 = x_286;
x_246 = x_289;
goto block_268;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_1);
x_290 = lean_string_utf8_next_fast(x_269, x_270);
lean_dec(x_270);
lean_inc(x_290);
lean_inc(x_269);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_269);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_unsigned_to_nat(1u);
x_293 = lean_nat_to_int(x_292);
x_294 = lean_int_neg(x_293);
lean_dec(x_293);
x_243 = x_291;
x_244 = x_269;
x_245 = x_290;
x_246 = x_294;
goto block_268;
}
}
}
}
block_31:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("expected 0-9", 12, 12);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Json_Parser_natCore(x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_System_Platform_numBits;
x_13 = lean_nat_pow(x_11, x_12);
x_14 = lean_nat_dec_lt(x_13, x_10);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_JsonNumber_shiftl(x_3, x_10);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_15);
return x_8;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_3);
x_16 = lean_mk_string_unchecked("exp too large", 13, 13);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_16);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_System_Platform_numBits;
x_21 = lean_nat_pow(x_19, x_20);
x_22 = lean_nat_dec_lt(x_21, x_18);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_JsonNumber_shiftl(x_3, x_18);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_3);
x_25 = lean_mk_string_unchecked("exp too large", 13, 13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
block_47:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_string_utf8_byte_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
x_38 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
uint32_t x_40; lean_object* x_41; uint32_t x_42; uint8_t x_43; 
x_40 = lean_string_utf8_get_fast(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_41 = lean_unsigned_to_nat(48u);
x_42 = l_Char_ofNat(x_41);
x_43 = lean_uint32_dec_le(x_42, x_40);
if (x_43 == 0)
{
x_2 = x_33;
x_3 = x_32;
x_4 = x_43;
goto block_31;
}
else
{
lean_object* x_44; uint32_t x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(57u);
x_45 = l_Char_ofNat(x_44);
x_46 = lean_uint32_dec_le(x_40, x_45);
x_2 = x_33;
x_3 = x_32;
x_4 = x_46;
goto block_31;
}
}
}
block_66:
{
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("expected 0-9", 12, 12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Json_Parser_natCore(x_53, x_48);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 1);
x_57 = l_Lean_JsonNumber_shiftr(x_49, x_56);
lean_dec(x_56);
lean_ctor_set(x_54, 1, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = l_Lean_JsonNumber_shiftr(x_49, x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_49);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
block_105:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_string_utf8_byte_size(x_67);
x_72 = lean_nat_dec_lt(x_69, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
x_73 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_68);
x_75 = lean_string_utf8_next_fast(x_67, x_69);
lean_dec(x_69);
lean_inc(x_75);
lean_inc(x_67);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_nat_dec_lt(x_75, x_71);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_67);
x_78 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
else
{
uint32_t x_80; lean_object* x_81; uint32_t x_82; uint8_t x_83; 
x_80 = lean_string_utf8_get_fast(x_67, x_75);
x_81 = lean_unsigned_to_nat(45u);
x_82 = l_Char_ofNat(x_81);
x_83 = l_instDecidableEqChar(x_80, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint32_t x_85; uint8_t x_86; 
lean_dec(x_71);
x_84 = lean_unsigned_to_nat(43u);
x_85 = l_Char_ofNat(x_84);
x_86 = l_instDecidableEqChar(x_80, x_85);
if (x_86 == 0)
{
x_32 = x_70;
x_33 = x_76;
x_34 = x_67;
x_35 = x_75;
goto block_47;
}
else
{
if (x_77 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_75);
lean_dec(x_70);
lean_dec(x_67);
x_87 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_76);
x_89 = lean_string_utf8_next_fast(x_67, x_75);
lean_dec(x_75);
lean_inc(x_89);
lean_inc(x_67);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_67);
lean_ctor_set(x_90, 1, x_89);
x_32 = x_70;
x_33 = x_90;
x_34 = x_67;
x_35 = x_89;
goto block_47;
}
}
}
else
{
if (x_77 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_67);
x_91 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_76);
x_93 = lean_string_utf8_next_fast(x_67, x_75);
lean_dec(x_75);
lean_inc(x_93);
lean_inc(x_67);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_67);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_nat_dec_lt(x_93, x_71);
lean_dec(x_71);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
lean_dec(x_70);
lean_dec(x_67);
x_96 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
else
{
uint32_t x_98; lean_object* x_99; uint32_t x_100; uint8_t x_101; 
x_98 = lean_string_utf8_get_fast(x_67, x_93);
lean_dec(x_93);
lean_dec(x_67);
x_99 = lean_unsigned_to_nat(48u);
x_100 = l_Char_ofNat(x_99);
x_101 = lean_uint32_dec_le(x_100, x_98);
if (x_101 == 0)
{
x_48 = x_94;
x_49 = x_70;
x_50 = x_101;
goto block_66;
}
else
{
lean_object* x_102; uint32_t x_103; uint8_t x_104; 
x_102 = lean_unsigned_to_nat(57u);
x_103 = l_Char_ofNat(x_102);
x_104 = lean_uint32_dec_le(x_98, x_103);
x_48 = x_94;
x_49 = x_70;
x_50 = x_104;
goto block_66;
}
}
}
}
}
}
}
block_123:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_string_utf8_byte_size(x_108);
x_111 = lean_nat_dec_lt(x_109, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_109);
lean_dec(x_108);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_106);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
else
{
if (x_111 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
x_113 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
else
{
uint32_t x_115; lean_object* x_116; uint32_t x_117; uint8_t x_118; 
x_115 = lean_string_utf8_get_fast(x_108, x_109);
x_116 = lean_unsigned_to_nat(101u);
x_117 = l_Char_ofNat(x_116);
x_118 = l_instDecidableEqChar(x_115, x_117);
if (x_118 == 0)
{
lean_object* x_119; uint32_t x_120; uint8_t x_121; 
x_119 = lean_unsigned_to_nat(69u);
x_120 = l_Char_ofNat(x_119);
x_121 = l_instDecidableEqChar(x_115, x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_109);
lean_dec(x_108);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_106);
lean_ctor_set(x_122, 1, x_107);
return x_122;
}
else
{
x_67 = x_108;
x_68 = x_106;
x_69 = x_109;
x_70 = x_107;
goto block_105;
}
}
else
{
x_67 = x_108;
x_68 = x_106;
x_69 = x_109;
x_70 = x_107;
goto block_105;
}
}
}
}
block_192:
{
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_126);
lean_dec(x_125);
x_128 = lean_mk_string_unchecked("expected digit", 14, 14);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_Json_Parser_natCoreNumDigits(x_130, x_130, x_124);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_131, 1);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_135 = lean_ctor_get(x_131, 0);
x_136 = lean_ctor_get(x_133, 0);
x_137 = lean_ctor_get(x_133, 1);
x_138 = lean_unsigned_to_nat(2u);
x_139 = l_System_Platform_numBits;
x_140 = lean_nat_pow(x_138, x_139);
x_141 = lean_nat_dec_lt(x_140, x_137);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_free_object(x_131);
x_142 = lean_nat_to_int(x_125);
x_143 = lean_unsigned_to_nat(10u);
x_144 = lean_nat_pow(x_143, x_137);
x_145 = lean_nat_to_int(x_144);
x_146 = lean_int_mul(x_142, x_145);
lean_dec(x_145);
lean_dec(x_142);
x_147 = lean_nat_to_int(x_136);
x_148 = lean_int_add(x_146, x_147);
lean_dec(x_147);
lean_dec(x_146);
x_149 = lean_int_mul(x_126, x_148);
lean_dec(x_148);
lean_dec(x_126);
lean_ctor_set(x_133, 0, x_149);
x_106 = x_135;
x_107 = x_133;
goto block_123;
}
else
{
lean_object* x_150; 
lean_free_object(x_133);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_126);
lean_dec(x_125);
x_150 = lean_mk_string_unchecked("too many decimals", 17, 17);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_150);
return x_131;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_151 = lean_ctor_get(x_131, 0);
x_152 = lean_ctor_get(x_133, 0);
x_153 = lean_ctor_get(x_133, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_133);
x_154 = lean_unsigned_to_nat(2u);
x_155 = l_System_Platform_numBits;
x_156 = lean_nat_pow(x_154, x_155);
x_157 = lean_nat_dec_lt(x_156, x_153);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_free_object(x_131);
x_158 = lean_nat_to_int(x_125);
x_159 = lean_unsigned_to_nat(10u);
x_160 = lean_nat_pow(x_159, x_153);
x_161 = lean_nat_to_int(x_160);
x_162 = lean_int_mul(x_158, x_161);
lean_dec(x_161);
lean_dec(x_158);
x_163 = lean_nat_to_int(x_152);
x_164 = lean_int_add(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
x_165 = lean_int_mul(x_126, x_164);
lean_dec(x_164);
lean_dec(x_126);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_153);
x_106 = x_151;
x_107 = x_166;
goto block_123;
}
else
{
lean_object* x_167; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_126);
lean_dec(x_125);
x_167 = lean_mk_string_unchecked("too many decimals", 17, 17);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_167);
return x_131;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_168 = lean_ctor_get(x_131, 1);
x_169 = lean_ctor_get(x_131, 0);
lean_inc(x_168);
lean_inc(x_169);
lean_dec(x_131);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_172 = x_168;
} else {
 lean_dec_ref(x_168);
 x_172 = lean_box(0);
}
x_173 = lean_unsigned_to_nat(2u);
x_174 = l_System_Platform_numBits;
x_175 = lean_nat_pow(x_173, x_174);
x_176 = lean_nat_dec_lt(x_175, x_171);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_177 = lean_nat_to_int(x_125);
x_178 = lean_unsigned_to_nat(10u);
x_179 = lean_nat_pow(x_178, x_171);
x_180 = lean_nat_to_int(x_179);
x_181 = lean_int_mul(x_177, x_180);
lean_dec(x_180);
lean_dec(x_177);
x_182 = lean_nat_to_int(x_170);
x_183 = lean_int_add(x_181, x_182);
lean_dec(x_182);
lean_dec(x_181);
x_184 = lean_int_mul(x_126, x_183);
lean_dec(x_183);
lean_dec(x_126);
if (lean_is_scalar(x_172)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_172;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_171);
x_106 = x_169;
x_107 = x_185;
goto block_123;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_126);
lean_dec(x_125);
x_186 = lean_mk_string_unchecked("too many decimals", 17, 17);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_169);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_126);
lean_dec(x_125);
x_188 = !lean_is_exclusive(x_131);
if (x_188 == 0)
{
return x_131;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_131, 0);
x_190 = lean_ctor_get(x_131, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_131);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
block_226:
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_string_utf8_byte_size(x_195);
x_199 = lean_nat_dec_lt(x_196, x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
x_200 = lean_nat_to_int(x_197);
x_201 = lean_int_mul(x_193, x_200);
lean_dec(x_200);
lean_dec(x_193);
x_202 = l_Lean_JsonNumber_fromInt(x_201);
x_106 = x_194;
x_107 = x_202;
goto block_123;
}
else
{
if (x_199 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_193);
x_203 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_194);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
uint32_t x_205; lean_object* x_206; uint32_t x_207; uint8_t x_208; 
x_205 = lean_string_utf8_get_fast(x_195, x_196);
x_206 = lean_unsigned_to_nat(46u);
x_207 = l_Char_ofNat(x_206);
x_208 = l_instDecidableEqChar(x_205, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
x_209 = lean_nat_to_int(x_197);
x_210 = lean_int_mul(x_193, x_209);
lean_dec(x_209);
lean_dec(x_193);
x_211 = l_Lean_JsonNumber_fromInt(x_210);
x_106 = x_194;
x_107 = x_211;
goto block_123;
}
else
{
if (x_199 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_193);
x_212 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_194);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_dec(x_194);
x_214 = lean_string_utf8_next_fast(x_195, x_196);
lean_dec(x_196);
lean_inc(x_214);
lean_inc(x_195);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_195);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_nat_dec_lt(x_214, x_198);
lean_dec(x_198);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_214);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_193);
x_217 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
else
{
uint32_t x_219; lean_object* x_220; uint32_t x_221; uint8_t x_222; 
x_219 = lean_string_utf8_get_fast(x_195, x_214);
lean_dec(x_214);
lean_dec(x_195);
x_220 = lean_unsigned_to_nat(48u);
x_221 = l_Char_ofNat(x_220);
x_222 = lean_uint32_dec_le(x_221, x_219);
if (x_222 == 0)
{
x_124 = x_215;
x_125 = x_197;
x_126 = x_193;
x_127 = x_222;
goto block_192;
}
else
{
lean_object* x_223; uint32_t x_224; uint8_t x_225; 
x_223 = lean_unsigned_to_nat(57u);
x_224 = l_Char_ofNat(x_223);
x_225 = lean_uint32_dec_le(x_219, x_224);
x_124 = x_215;
x_125 = x_197;
x_126 = x_193;
x_127 = x_225;
goto block_192;
}
}
}
}
}
}
}
block_242:
{
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_228);
x_230 = lean_mk_string_unchecked("expected 1-9", 12, 12);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_unsigned_to_nat(0u);
x_233 = l_Lean_Json_Parser_natCore(x_232, x_227);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
x_193 = x_228;
x_194 = x_234;
x_195 = x_236;
x_196 = x_237;
x_197 = x_235;
goto block_226;
}
else
{
uint8_t x_238; 
lean_dec(x_228);
x_238 = !lean_is_exclusive(x_233);
if (x_238 == 0)
{
return x_233;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_233, 0);
x_240 = lean_ctor_get(x_233, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_233);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
block_268:
{
lean_object* x_247; uint8_t x_248; 
x_247 = lean_string_utf8_byte_size(x_244);
x_248 = lean_nat_dec_lt(x_245, x_247);
lean_dec(x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_249 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
else
{
uint32_t x_251; lean_object* x_252; uint32_t x_253; uint8_t x_254; 
x_251 = lean_string_utf8_get_fast(x_244, x_245);
x_252 = lean_unsigned_to_nat(48u);
x_253 = l_Char_ofNat(x_252);
x_254 = l_instDecidableEqChar(x_251, x_253);
if (x_254 == 0)
{
lean_dec(x_245);
lean_dec(x_244);
if (x_248 == 0)
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_246);
x_255 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_243);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
else
{
lean_object* x_257; uint32_t x_258; uint8_t x_259; 
x_257 = lean_unsigned_to_nat(49u);
x_258 = l_Char_ofNat(x_257);
x_259 = lean_uint32_dec_le(x_258, x_251);
if (x_259 == 0)
{
x_227 = x_243;
x_228 = x_246;
x_229 = x_259;
goto block_242;
}
else
{
lean_object* x_260; uint32_t x_261; uint8_t x_262; 
x_260 = lean_unsigned_to_nat(57u);
x_261 = l_Char_ofNat(x_260);
x_262 = lean_uint32_dec_le(x_251, x_261);
x_227 = x_243;
x_228 = x_246;
x_229 = x_262;
goto block_242;
}
}
}
else
{
if (x_248 == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_263 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_243);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_243);
x_265 = lean_string_utf8_next_fast(x_244, x_245);
lean_dec(x_245);
lean_inc(x_265);
lean_inc(x_244);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_244);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_unsigned_to_nat(0u);
x_193 = x_246;
x_194 = x_266;
x_195 = x_244;
x_196 = x_265;
x_197 = x_267;
goto block_226;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_arrayCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_Parser_anyCore(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_5, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = lean_array_push(x_1, x_6);
x_16 = lean_string_utf8_get_fast(x_7, x_8);
x_17 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_17);
x_18 = lean_unsigned_to_nat(93u);
x_19 = l_Char_ofNat(x_18);
x_20 = l_instDecidableEqChar(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(44u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_instDecidableEqChar(x_16, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_15);
x_24 = lean_mk_string_unchecked("unexpected character in array", 29, 29);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_24);
return x_3;
}
else
{
lean_object* x_25; 
lean_free_object(x_3);
x_25 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_5);
x_1 = x_15;
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; 
x_27 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_5);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
}
else
{
lean_object* x_28; uint32_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; uint8_t x_34; 
lean_dec(x_5);
x_28 = lean_array_push(x_1, x_6);
x_29 = lean_string_utf8_get_fast(x_7, x_8);
x_30 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(93u);
x_33 = l_Char_ofNat(x_32);
x_34 = l_instDecidableEqChar(x_29, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(44u);
x_36 = l_Char_ofNat(x_35);
x_37 = l_instDecidableEqChar(x_29, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_28);
x_38 = lean_mk_string_unchecked("unexpected character in array", 29, 29);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_38);
lean_ctor_set(x_3, 0, x_31);
return x_3;
}
else
{
lean_object* x_39; 
lean_free_object(x_3);
x_39 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_31);
x_1 = x_28;
x_2 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; 
x_41 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_31);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_41);
return x_3;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_3);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_string_utf8_byte_size(x_44);
x_47 = lean_nat_dec_lt(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_1);
x_48 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint32_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint32_t x_56; uint8_t x_57; 
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
x_51 = lean_array_push(x_1, x_43);
x_52 = lean_string_utf8_get_fast(x_44, x_45);
x_53 = lean_string_utf8_next_fast(x_44, x_45);
lean_dec(x_45);
if (lean_is_scalar(x_50)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_50;
}
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_unsigned_to_nat(93u);
x_56 = l_Char_ofNat(x_55);
x_57 = l_instDecidableEqChar(x_52, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint32_t x_59; uint8_t x_60; 
x_58 = lean_unsigned_to_nat(44u);
x_59 = l_Char_ofNat(x_58);
x_60 = l_instDecidableEqChar(x_52, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
x_61 = lean_mk_string_unchecked("unexpected character in array", 29, 29);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
else
{
lean_object* x_63; 
x_63 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_54);
x_1 = x_51;
x_2 = x_63;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_54);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_51);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_3);
if (x_67 == 0)
{
return x_3;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get(x_3, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_3);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_anyCore(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_string_utf8_byte_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_21);
x_25 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
uint32_t x_27; lean_object* x_28; uint32_t x_29; uint8_t x_30; 
x_27 = lean_string_utf8_get_fast(x_21, x_22);
x_28 = lean_unsigned_to_nat(91u);
x_29 = l_Char_ofNat(x_28);
x_30 = l_instDecidableEqChar(x_27, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(123u);
x_32 = l_Char_ofNat(x_31);
x_33 = l_instDecidableEqChar(x_27, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_34 = lean_unsigned_to_nat(34u);
x_35 = l_Char_ofNat(x_34);
x_36 = l_instDecidableEqChar(x_27, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint32_t x_38; uint8_t x_39; 
lean_dec(x_22);
lean_dec(x_21);
x_37 = lean_unsigned_to_nat(102u);
x_38 = l_Char_ofNat(x_37);
x_39 = l_instDecidableEqChar(x_27, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint32_t x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(116u);
x_41 = l_Char_ofNat(x_40);
x_42 = l_instDecidableEqChar(x_27, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(110u);
x_44 = l_Char_ofNat(x_43);
x_45 = l_instDecidableEqChar(x_27, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint32_t x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(45u);
x_47 = l_Char_ofNat(x_46);
x_48 = l_instDecidableEqChar(x_27, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint32_t x_50; uint8_t x_51; 
x_49 = lean_unsigned_to_nat(48u);
x_50 = l_Char_ofNat(x_49);
x_51 = lean_uint32_dec_le(x_50, x_27);
if (x_51 == 0)
{
x_2 = x_51;
goto block_20;
}
else
{
lean_object* x_52; uint32_t x_53; uint8_t x_54; 
x_52 = lean_unsigned_to_nat(57u);
x_53 = l_Char_ofNat(x_52);
x_54 = lean_uint32_dec_le(x_27, x_53);
x_2 = x_54;
goto block_20;
}
}
else
{
x_2 = x_24;
goto block_20;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Std_Internal_Parsec_String_pstring(x_55, x_1);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_dec(x_59);
x_60 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_58);
x_61 = lean_box(0);
lean_ctor_set(x_56, 1, x_61);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_62);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
return x_56;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_mk_string_unchecked("true", 4, 4);
x_71 = l_Std_Internal_Parsec_String_pstring(x_70, x_1);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_dec(x_74);
x_75 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_73);
x_76 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_76, 0, x_24);
lean_ctor_set(x_71, 1, x_76);
lean_ctor_set(x_71, 0, x_75);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
lean_dec(x_71);
x_78 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_77);
x_79 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_79, 0, x_24);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_71);
if (x_81 == 0)
{
return x_71;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_71, 0);
x_83 = lean_ctor_get(x_71, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_71);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_mk_string_unchecked("false", 5, 5);
x_86 = l_Std_Internal_Parsec_String_pstring(x_85, x_1);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_dec(x_89);
x_90 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_88);
x_91 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_91, 0, x_36);
lean_ctor_set(x_86, 1, x_91);
lean_ctor_set(x_86, 0, x_90);
return x_86;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
lean_dec(x_86);
x_93 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_92);
x_94 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_94, 0, x_36);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_86);
if (x_96 == 0)
{
return x_86;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_86, 0);
x_98 = lean_ctor_get(x_86, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_86);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
if (x_24 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_22);
lean_dec(x_21);
x_100 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_1);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_1, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_1, 0);
lean_dec(x_104);
x_105 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_105);
x_106 = lean_mk_string_unchecked("", 0, 0);
x_107 = l_Lean_Json_Parser_strCore(x_106, x_1);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_109);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_107, 1, x_112);
lean_ctor_set(x_107, 0, x_111);
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_115 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_113);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_107);
if (x_118 == 0)
{
return x_107;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_107, 0);
x_120 = lean_ctor_get(x_107, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_107);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_122 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_21);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_mk_string_unchecked("", 0, 0);
x_125 = l_Lean_Json_Parser_strCore(x_124, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_126);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_127);
if (lean_is_scalar(x_128)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_128;
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_134 = x_125;
} else {
 lean_dec_ref(x_125);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
}
}
else
{
if (x_24 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_22);
lean_dec(x_21);
x_136 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_1);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_139 = lean_ctor_get(x_1, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_1, 0);
lean_dec(x_140);
x_141 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_141);
x_142 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
x_145 = lean_string_utf8_byte_size(x_143);
x_146 = lean_nat_dec_lt(x_144, x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_144);
lean_dec(x_143);
x_147 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
else
{
uint32_t x_149; lean_object* x_150; uint32_t x_151; uint8_t x_152; 
x_149 = lean_string_utf8_get_fast(x_143, x_144);
lean_dec(x_144);
lean_dec(x_143);
x_150 = lean_unsigned_to_nat(125u);
x_151 = l_Char_ofNat(x_150);
x_152 = l_instDecidableEqChar(x_149, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_box(0);
x_154 = l_Lean_Json_Parser_objectCore(x_153, x_142);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_154, 1);
x_157 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_154, 1, x_157);
return x_154;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_154, 0);
x_159 = lean_ctor_get(x_154, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_154);
x_160 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_154);
if (x_162 == 0)
{
return x_154;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_154, 0);
x_164 = lean_ctor_get(x_154, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_154);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_142, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_142, 1);
lean_inc(x_167);
x_168 = lean_string_utf8_byte_size(x_166);
x_169 = lean_nat_dec_lt(x_167, x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_167);
lean_dec(x_166);
x_170 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_142);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_142);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_142, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_142, 0);
lean_dec(x_174);
x_175 = lean_string_utf8_next_fast(x_166, x_167);
lean_dec(x_167);
lean_ctor_set(x_142, 1, x_175);
x_176 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_142);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_142);
x_180 = lean_string_utf8_next_fast(x_166, x_167);
lean_dec(x_167);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_166);
lean_ctor_set(x_181, 1, x_180);
x_182 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_181);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
lean_dec(x_1);
x_186 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_21);
lean_ctor_set(x_187, 1, x_186);
x_188 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
x_191 = lean_string_utf8_byte_size(x_189);
x_192 = lean_nat_dec_lt(x_190, x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_190);
lean_dec(x_189);
x_193 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_188);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
else
{
uint32_t x_195; lean_object* x_196; uint32_t x_197; uint8_t x_198; 
x_195 = lean_string_utf8_get_fast(x_189, x_190);
lean_dec(x_190);
lean_dec(x_189);
x_196 = lean_unsigned_to_nat(125u);
x_197 = l_Char_ofNat(x_196);
x_198 = l_instDecidableEqChar(x_195, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_box(0);
x_200 = l_Lean_Json_Parser_objectCore(x_199, x_188);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_204, 0, x_202);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_188, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_188, 1);
lean_inc(x_211);
x_212 = lean_string_utf8_byte_size(x_210);
x_213 = lean_nat_dec_lt(x_211, x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_211);
lean_dec(x_210);
x_214 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_188);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_216 = x_188;
} else {
 lean_dec_ref(x_188);
 x_216 = lean_box(0);
}
x_217 = lean_string_utf8_next_fast(x_210, x_211);
lean_dec(x_211);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_210);
lean_ctor_set(x_218, 1, x_217);
x_219 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_218);
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
}
}
}
else
{
if (x_24 == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_22);
lean_dec(x_21);
x_223 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_1);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
else
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_1);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_226 = lean_ctor_get(x_1, 1);
lean_dec(x_226);
x_227 = lean_ctor_get(x_1, 0);
lean_dec(x_227);
x_228 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_228);
x_229 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
x_232 = lean_string_utf8_byte_size(x_230);
x_233 = lean_nat_dec_lt(x_231, x_232);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_231);
lean_dec(x_230);
x_234 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
else
{
uint32_t x_236; lean_object* x_237; uint32_t x_238; uint8_t x_239; 
x_236 = lean_string_utf8_get_fast(x_230, x_231);
lean_dec(x_231);
lean_dec(x_230);
x_237 = lean_unsigned_to_nat(93u);
x_238 = l_Char_ofNat(x_237);
x_239 = l_instDecidableEqChar(x_236, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_unsigned_to_nat(4u);
x_241 = lean_mk_empty_array_with_capacity(x_240);
x_242 = l_Lean_Json_Parser_arrayCore(x_241, x_229);
if (lean_obj_tag(x_242) == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_242, 1);
x_245 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_242, 1, x_245);
return x_242;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_242, 0);
x_247 = lean_ctor_get(x_242, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_242);
x_248 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_242);
if (x_250 == 0)
{
return x_242;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_242, 0);
x_252 = lean_ctor_get(x_242, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_242);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = lean_ctor_get(x_229, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_229, 1);
lean_inc(x_255);
x_256 = lean_string_utf8_byte_size(x_254);
x_257 = lean_nat_dec_lt(x_255, x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_255);
lean_dec(x_254);
x_258 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_229);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
else
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_229);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_229, 1);
lean_dec(x_261);
x_262 = lean_ctor_get(x_229, 0);
lean_dec(x_262);
x_263 = lean_string_utf8_next_fast(x_254, x_255);
lean_dec(x_255);
lean_ctor_set(x_229, 1, x_263);
x_264 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_229);
x_265 = lean_unsigned_to_nat(0u);
x_266 = lean_mk_empty_array_with_capacity(x_265);
x_267 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_229);
x_269 = lean_string_utf8_next_fast(x_254, x_255);
lean_dec(x_255);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_254);
lean_ctor_set(x_270, 1, x_269);
x_271 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_270);
x_272 = lean_unsigned_to_nat(0u);
x_273 = lean_mk_empty_array_with_capacity(x_272);
x_274 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_271);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec(x_1);
x_276 = lean_string_utf8_next_fast(x_21, x_22);
lean_dec(x_22);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_21);
lean_ctor_set(x_277, 1, x_276);
x_278 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_277);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
x_281 = lean_string_utf8_byte_size(x_279);
x_282 = lean_nat_dec_lt(x_280, x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_280);
lean_dec(x_279);
x_283 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_278);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
else
{
uint32_t x_285; lean_object* x_286; uint32_t x_287; uint8_t x_288; 
x_285 = lean_string_utf8_get_fast(x_279, x_280);
lean_dec(x_280);
lean_dec(x_279);
x_286 = lean_unsigned_to_nat(93u);
x_287 = l_Char_ofNat(x_286);
x_288 = l_instDecidableEqChar(x_285, x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_unsigned_to_nat(4u);
x_290 = lean_mk_empty_array_with_capacity(x_289);
x_291 = l_Lean_Json_Parser_arrayCore(x_290, x_278);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_294 = x_291;
} else {
 lean_dec_ref(x_291);
 x_294 = lean_box(0);
}
x_295 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_295, 0, x_293);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_292);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_291, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_291, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_299 = x_291;
} else {
 lean_dec_ref(x_291);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = lean_ctor_get(x_278, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_278, 1);
lean_inc(x_302);
x_303 = lean_string_utf8_byte_size(x_301);
x_304 = lean_nat_dec_lt(x_302, x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_302);
lean_dec(x_301);
x_305 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_278);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_307 = x_278;
} else {
 lean_dec_ref(x_278);
 x_307 = lean_box(0);
}
x_308 = lean_string_utf8_next_fast(x_301, x_302);
lean_dec(x_302);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_301);
lean_ctor_set(x_309, 1, x_308);
x_310 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_309);
x_311 = lean_unsigned_to_nat(0u);
x_312 = lean_mk_empty_array_with_capacity(x_311);
x_313 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_310);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
}
}
}
}
block_20:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("unexpected input", 16, 16);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Json_Parser_num(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_7);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_objectCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = lean_unsigned_to_nat(34u);
x_11 = l_Char_ofNat(x_10);
x_12 = l_instDecidableEqChar(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("expected \"", 10, 10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
if (x_6 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_20);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_Json_Parser_strCore(x_21, x_2);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_string_utf8_byte_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_1);
x_31 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
uint32_t x_32; lean_object* x_33; uint32_t x_34; uint8_t x_35; 
x_32 = lean_string_utf8_get_fast(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_33 = lean_unsigned_to_nat(58u);
x_34 = l_Char_ofNat(x_33);
x_35 = l_instDecidableEqChar(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_25);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("expected :", 10, 10);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_36);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
x_39 = lean_string_utf8_byte_size(x_37);
x_40 = lean_nat_dec_lt(x_38, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_1);
x_41 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_41);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
uint8_t x_42; 
lean_free_object(x_22);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_26, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_26, 0);
lean_dec(x_44);
x_45 = lean_string_utf8_next_fast(x_37, x_38);
lean_dec(x_38);
lean_ctor_set(x_26, 1, x_45);
x_46 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_26);
x_47 = l_Lean_Json_Parser_anyCore(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_string_utf8_byte_size(x_51);
x_54 = lean_nat_dec_lt(x_52, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_25);
lean_dec(x_1);
x_55 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 1, x_55);
return x_47;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint32_t x_59; lean_object* x_60; lean_object* x_61; uint32_t x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_49, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_49, 0);
lean_dec(x_58);
x_59 = lean_string_utf8_get_fast(x_51, x_52);
x_60 = lean_string_utf8_next_fast(x_51, x_52);
lean_dec(x_52);
lean_ctor_set(x_49, 1, x_60);
x_61 = lean_unsigned_to_nat(125u);
x_62 = l_Char_ofNat(x_61);
x_63 = l_instDecidableEqChar(x_59, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint32_t x_65; uint8_t x_66; 
x_64 = lean_unsigned_to_nat(44u);
x_65 = l_Char_ofNat(x_64);
x_66 = l_instDecidableEqChar(x_59, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_50);
lean_dec(x_25);
lean_dec(x_1);
x_67 = lean_mk_string_unchecked("unexpected character in object", 30, 30);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 1, x_67);
return x_47;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_free_object(x_47);
x_68 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_49);
x_69 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_50);
x_1 = x_69;
x_2 = x_68;
goto _start;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_49);
x_72 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_50);
lean_ctor_set(x_47, 1, x_72);
lean_ctor_set(x_47, 0, x_71);
return x_47;
}
}
else
{
uint32_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint32_t x_77; uint8_t x_78; 
lean_dec(x_49);
x_73 = lean_string_utf8_get_fast(x_51, x_52);
x_74 = lean_string_utf8_next_fast(x_51, x_52);
lean_dec(x_52);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_51);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_unsigned_to_nat(125u);
x_77 = l_Char_ofNat(x_76);
x_78 = l_instDecidableEqChar(x_73, x_77);
if (x_78 == 0)
{
lean_object* x_79; uint32_t x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(44u);
x_80 = l_Char_ofNat(x_79);
x_81 = l_instDecidableEqChar(x_73, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_50);
lean_dec(x_25);
lean_dec(x_1);
x_82 = lean_mk_string_unchecked("unexpected character in object", 30, 30);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 1, x_82);
lean_ctor_set(x_47, 0, x_75);
return x_47;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_free_object(x_47);
x_83 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_75);
x_84 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_50);
x_1 = x_84;
x_2 = x_83;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_75);
x_87 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_50);
lean_ctor_set(x_47, 1, x_87);
lean_ctor_set(x_47, 0, x_86);
return x_47;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_47, 0);
x_89 = lean_ctor_get(x_47, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_47);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
x_92 = lean_string_utf8_byte_size(x_90);
x_93 = lean_nat_dec_lt(x_91, x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_25);
lean_dec(x_1);
x_94 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; uint32_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint32_t x_101; uint8_t x_102; 
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
x_97 = lean_string_utf8_get_fast(x_90, x_91);
x_98 = lean_string_utf8_next_fast(x_90, x_91);
lean_dec(x_91);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_90);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_unsigned_to_nat(125u);
x_101 = l_Char_ofNat(x_100);
x_102 = l_instDecidableEqChar(x_97, x_101);
if (x_102 == 0)
{
lean_object* x_103; uint32_t x_104; uint8_t x_105; 
x_103 = lean_unsigned_to_nat(44u);
x_104 = l_Char_ofNat(x_103);
x_105 = l_instDecidableEqChar(x_97, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_89);
lean_dec(x_25);
lean_dec(x_1);
x_106 = lean_mk_string_unchecked("unexpected character in object", 30, 30);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_99);
x_109 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_89);
x_1 = x_109;
x_2 = x_108;
goto _start;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_99);
x_112 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_89);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_25);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_47);
if (x_114 == 0)
{
return x_47;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_47, 0);
x_116 = lean_ctor_get(x_47, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_47);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_26);
x_118 = lean_string_utf8_next_fast(x_37, x_38);
lean_dec(x_38);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_118);
x_120 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_119);
x_121 = l_Lean_Json_Parser_anyCore(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
x_127 = lean_string_utf8_byte_size(x_125);
x_128 = lean_nat_dec_lt(x_126, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_25);
lean_dec(x_1);
x_129 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_124;
 lean_ctor_set_tag(x_130, 1);
}
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
else
{
lean_object* x_131; uint32_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint32_t x_136; uint8_t x_137; 
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_131 = x_122;
} else {
 lean_dec_ref(x_122);
 x_131 = lean_box(0);
}
x_132 = lean_string_utf8_get_fast(x_125, x_126);
x_133 = lean_string_utf8_next_fast(x_125, x_126);
lean_dec(x_126);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_unsigned_to_nat(125u);
x_136 = l_Char_ofNat(x_135);
x_137 = l_instDecidableEqChar(x_132, x_136);
if (x_137 == 0)
{
lean_object* x_138; uint32_t x_139; uint8_t x_140; 
x_138 = lean_unsigned_to_nat(44u);
x_139 = l_Char_ofNat(x_138);
x_140 = l_instDecidableEqChar(x_132, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_123);
lean_dec(x_25);
lean_dec(x_1);
x_141 = lean_mk_string_unchecked("unexpected character in object", 30, 30);
if (lean_is_scalar(x_124)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_124;
 lean_ctor_set_tag(x_142, 1);
}
lean_ctor_set(x_142, 0, x_134);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_124);
x_143 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_134);
x_144 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_123);
x_1 = x_144;
x_2 = x_143;
goto _start;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_134);
x_147 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_25, x_123);
if (lean_is_scalar(x_124)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_124;
}
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_25);
lean_dec(x_1);
x_149 = lean_ctor_get(x_121, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_121, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_151 = x_121;
} else {
 lean_dec_ref(x_121);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_153 = lean_ctor_get(x_22, 0);
x_154 = lean_ctor_get(x_22, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_22);
x_155 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_153);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = lean_string_utf8_byte_size(x_156);
x_159 = lean_nat_dec_lt(x_157, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_1);
x_160 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
else
{
uint32_t x_162; lean_object* x_163; uint32_t x_164; uint8_t x_165; 
x_162 = lean_string_utf8_get_fast(x_156, x_157);
lean_dec(x_157);
lean_dec(x_156);
x_163 = lean_unsigned_to_nat(58u);
x_164 = l_Char_ofNat(x_163);
x_165 = l_instDecidableEqChar(x_162, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_154);
lean_dec(x_1);
x_166 = lean_mk_string_unchecked("expected :", 10, 10);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_155);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_ctor_get(x_155, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_155, 1);
lean_inc(x_169);
x_170 = lean_string_utf8_byte_size(x_168);
x_171 = lean_nat_dec_lt(x_169, x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_154);
lean_dec(x_1);
x_172 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_155);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_174 = x_155;
} else {
 lean_dec_ref(x_155);
 x_174 = lean_box(0);
}
x_175 = lean_string_utf8_next_fast(x_168, x_169);
lean_dec(x_169);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_175);
x_177 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_176);
x_178 = l_Lean_Json_Parser_anyCore(x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_179, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
x_184 = lean_string_utf8_byte_size(x_182);
x_185 = lean_nat_dec_lt(x_183, x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_154);
lean_dec(x_1);
x_186 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_181)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_181;
 lean_ctor_set_tag(x_187, 1);
}
lean_ctor_set(x_187, 0, x_179);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
else
{
lean_object* x_188; uint32_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint32_t x_193; uint8_t x_194; 
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_188 = x_179;
} else {
 lean_dec_ref(x_179);
 x_188 = lean_box(0);
}
x_189 = lean_string_utf8_get_fast(x_182, x_183);
x_190 = lean_string_utf8_next_fast(x_182, x_183);
lean_dec(x_183);
if (lean_is_scalar(x_188)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_188;
}
lean_ctor_set(x_191, 0, x_182);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_unsigned_to_nat(125u);
x_193 = l_Char_ofNat(x_192);
x_194 = l_instDecidableEqChar(x_189, x_193);
if (x_194 == 0)
{
lean_object* x_195; uint32_t x_196; uint8_t x_197; 
x_195 = lean_unsigned_to_nat(44u);
x_196 = l_Char_ofNat(x_195);
x_197 = l_instDecidableEqChar(x_189, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_180);
lean_dec(x_154);
lean_dec(x_1);
x_198 = lean_mk_string_unchecked("unexpected character in object", 30, 30);
if (lean_is_scalar(x_181)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_181;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_191);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_181);
x_200 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_191);
x_201 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_154, x_180);
x_1 = x_201;
x_2 = x_200;
goto _start;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_191);
x_204 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_154, x_180);
if (lean_is_scalar(x_181)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_181;
}
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_154);
lean_dec(x_1);
x_206 = lean_ctor_get(x_178, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_178, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_208 = x_178;
} else {
 lean_dec_ref(x_178);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_22);
if (x_210 == 0)
{
return x_22;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_22, 0);
x_212 = lean_ctor_get(x_22, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_22);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_2);
x_214 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_3);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_mk_string_unchecked("", 0, 0);
x_217 = l_Lean_Json_Parser_strCore(x_216, x_215);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_218);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
x_224 = lean_string_utf8_byte_size(x_222);
x_225 = lean_nat_dec_lt(x_223, x_224);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_1);
x_226 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_220)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_220;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_221);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
else
{
uint32_t x_228; lean_object* x_229; uint32_t x_230; uint8_t x_231; 
x_228 = lean_string_utf8_get_fast(x_222, x_223);
lean_dec(x_223);
lean_dec(x_222);
x_229 = lean_unsigned_to_nat(58u);
x_230 = l_Char_ofNat(x_229);
x_231 = l_instDecidableEqChar(x_228, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_219);
lean_dec(x_1);
x_232 = lean_mk_string_unchecked("expected :", 10, 10);
if (lean_is_scalar(x_220)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_220;
 lean_ctor_set_tag(x_233, 1);
}
lean_ctor_set(x_233, 0, x_221);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_234 = lean_ctor_get(x_221, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_221, 1);
lean_inc(x_235);
x_236 = lean_string_utf8_byte_size(x_234);
x_237 = lean_nat_dec_lt(x_235, x_236);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_219);
lean_dec(x_1);
x_238 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_220)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_220;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_221);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_220);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_240 = x_221;
} else {
 lean_dec_ref(x_221);
 x_240 = lean_box(0);
}
x_241 = lean_string_utf8_next_fast(x_234, x_235);
lean_dec(x_235);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_234);
lean_ctor_set(x_242, 1, x_241);
x_243 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_242);
x_244 = l_Lean_Json_Parser_anyCore(x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_245, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
x_250 = lean_string_utf8_byte_size(x_248);
x_251 = lean_nat_dec_lt(x_249, x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_219);
lean_dec(x_1);
x_252 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_247)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_247;
 lean_ctor_set_tag(x_253, 1);
}
lean_ctor_set(x_253, 0, x_245);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
else
{
lean_object* x_254; uint32_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint32_t x_259; uint8_t x_260; 
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_254 = x_245;
} else {
 lean_dec_ref(x_245);
 x_254 = lean_box(0);
}
x_255 = lean_string_utf8_get_fast(x_248, x_249);
x_256 = lean_string_utf8_next_fast(x_248, x_249);
lean_dec(x_249);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_254;
}
lean_ctor_set(x_257, 0, x_248);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_unsigned_to_nat(125u);
x_259 = l_Char_ofNat(x_258);
x_260 = l_instDecidableEqChar(x_255, x_259);
if (x_260 == 0)
{
lean_object* x_261; uint32_t x_262; uint8_t x_263; 
x_261 = lean_unsigned_to_nat(44u);
x_262 = l_Char_ofNat(x_261);
x_263 = l_instDecidableEqChar(x_255, x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_246);
lean_dec(x_219);
lean_dec(x_1);
x_264 = lean_mk_string_unchecked("unexpected character in object", 30, 30);
if (lean_is_scalar(x_247)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_247;
 lean_ctor_set_tag(x_265, 1);
}
lean_ctor_set(x_265, 0, x_257);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_247);
x_266 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_257);
x_267 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_219, x_246);
x_1 = x_267;
x_2 = x_266;
goto _start;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_257);
x_270 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_1, x_219, x_246);
if (lean_is_scalar(x_247)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_247;
}
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_219);
lean_dec(x_1);
x_272 = lean_ctor_get(x_244, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_244, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_274 = x_244;
} else {
 lean_dec_ref(x_244);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_1);
x_276 = lean_ctor_get(x_217, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_217, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_278 = x_217;
} else {
 lean_dec_ref(x_217);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_Parser_any(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_3 = l_Lean_Json_Parser_anyCore(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
lean_dec(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = lean_mk_string_unchecked("expected end of input", 21, 21);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_mk_string_unchecked("expected end of input", 21, 21);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
x_3 = l_Std_Internal_Parsec_String_Parser_run(lean_box(0), x_2, x_1);
return x_3;
}
}
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Parser(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
