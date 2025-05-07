// Lean compiler output
// Module: Lake.CLI.Error
// Imports: Init.Data.ToString Init.System.FilePath
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedCliError;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_toString___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprCliError;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT uint8_t l_Lake_CliError_toString___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object*);
lean_object* l_Char_quote(uint32_t);
lean_object* l_List_repr_x27___at_____private_Init_Meta_0__Lean_Syntax_reprPreresolved____x40_Init_Meta___hyg_1912__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_CliError_instToString;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_324_(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_324____boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedCliError() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_324_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; lean_object* x_30; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_nat_to_int(x_41);
x_21 = x_42;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_to_int(x_43);
x_21 = x_44;
goto block_29;
}
}
case 1:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_61; uint8_t x_62; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_46 = x_1;
} else {
 lean_dec_ref(x_1);
 x_46 = lean_box(0);
}
x_61 = lean_unsigned_to_nat(1024u);
x_62 = lean_nat_dec_le(x_61, x_2);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_nat_to_int(x_63);
x_47 = x_64;
goto block_60;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_to_int(x_65);
x_47 = x_66;
goto block_60;
}
block_60:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_48 = lean_mk_string_unchecked("Lake.CliError.unknownCommand", 28, 28);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(3, 1, 0);
} else {
 x_49 = x_46;
 lean_ctor_set_tag(x_49, 3);
}
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_box(1);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_String_quote(x_45);
lean_dec(x_45);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_unbox(x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
x_59 = l_Repr_addAppParen(x_57, x_2);
return x_59;
}
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_83; uint8_t x_84; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_68 = x_1;
} else {
 lean_dec_ref(x_1);
 x_68 = lean_box(0);
}
x_83 = lean_unsigned_to_nat(1024u);
x_84 = lean_nat_dec_le(x_83, x_2);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_to_int(x_85);
x_69 = x_86;
goto block_82;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_to_int(x_87);
x_69 = x_88;
goto block_82;
}
block_82:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_70 = lean_mk_string_unchecked("Lake.CliError.missingArg", 24, 24);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(3, 1, 0);
} else {
 x_71 = x_68;
 lean_ctor_set_tag(x_71, 3);
}
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_box(1);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_String_quote(x_67);
lean_dec(x_67);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_79, 0, x_77);
x_80 = lean_unbox(x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_80);
x_81 = l_Repr_addAppParen(x_79, x_2);
return x_81;
}
}
case 3:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_110; uint8_t x_111; 
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_91 = x_1;
} else {
 lean_dec_ref(x_1);
 x_91 = lean_box(0);
}
x_110 = lean_unsigned_to_nat(1024u);
x_111 = lean_nat_dec_le(x_110, x_2);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_unsigned_to_nat(2u);
x_113 = lean_nat_to_int(x_112);
x_92 = x_113;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_to_int(x_114);
x_92 = x_115;
goto block_109;
}
block_109:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_93 = lean_mk_string_unchecked("Lake.CliError.missingOptArg", 27, 27);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_box(1);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(5, 2, 0);
} else {
 x_96 = x_91;
 lean_ctor_set_tag(x_96, 5);
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_String_quote(x_89);
lean_dec(x_89);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
x_101 = l_String_quote(x_90);
lean_dec(x_90);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_104, 0, x_92);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_106, 0, x_104);
x_107 = lean_unbox(x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_107);
x_108 = l_Repr_addAppParen(x_106, x_2);
return x_108;
}
}
case 4:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_137; uint8_t x_138; 
x_116 = lean_ctor_get(x_1, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_1, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_118 = x_1;
} else {
 lean_dec_ref(x_1);
 x_118 = lean_box(0);
}
x_137 = lean_unsigned_to_nat(1024u);
x_138 = lean_nat_dec_le(x_137, x_2);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_to_int(x_139);
x_119 = x_140;
goto block_136;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_to_int(x_141);
x_119 = x_142;
goto block_136;
}
block_136:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; 
x_120 = lean_mk_string_unchecked("Lake.CliError.invalidOptArg", 27, 27);
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_box(1);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(5, 2, 0);
} else {
 x_123 = x_118;
 lean_ctor_set_tag(x_123, 5);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_String_quote(x_116);
lean_dec(x_116);
x_125 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_122);
x_128 = l_String_quote(x_117);
lean_dec(x_117);
x_129 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_131, 0, x_119);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_133, 0, x_131);
x_134 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_134);
x_135 = l_Repr_addAppParen(x_133, x_2);
return x_135;
}
}
case 5:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_160; uint8_t x_161; 
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_144 = x_1;
} else {
 lean_dec_ref(x_1);
 x_144 = lean_box(0);
}
x_160 = lean_unsigned_to_nat(1024u);
x_161 = lean_nat_dec_le(x_160, x_2);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_unsigned_to_nat(2u);
x_163 = lean_nat_to_int(x_162);
x_145 = x_163;
goto block_159;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_to_int(x_164);
x_145 = x_165;
goto block_159;
}
block_159:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint32_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_146 = lean_mk_string_unchecked("Lake.CliError.unknownShortOption", 32, 32);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(3, 1, 0);
} else {
 x_147 = x_144;
 lean_ctor_set_tag(x_147, 3);
}
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_box(1);
x_149 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_unbox_uint32(x_143);
lean_dec(x_143);
x_151 = l_Char_quote(x_150);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_156, 0, x_154);
x_157 = lean_unbox(x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_157);
x_158 = l_Repr_addAppParen(x_156, x_2);
return x_158;
}
}
case 6:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_182; uint8_t x_183; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_167 = x_1;
} else {
 lean_dec_ref(x_1);
 x_167 = lean_box(0);
}
x_182 = lean_unsigned_to_nat(1024u);
x_183 = lean_nat_dec_le(x_182, x_2);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_unsigned_to_nat(2u);
x_185 = lean_nat_to_int(x_184);
x_168 = x_185;
goto block_181;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_to_int(x_186);
x_168 = x_187;
goto block_181;
}
block_181:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_169 = lean_mk_string_unchecked("Lake.CliError.unknownLongOption", 31, 31);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(3, 1, 0);
} else {
 x_170 = x_167;
 lean_ctor_set_tag(x_170, 3);
}
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_box(1);
x_172 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_String_quote(x_166);
lean_dec(x_166);
x_174 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_178, 0, x_176);
x_179 = lean_unbox(x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_179);
x_180 = l_Repr_addAppParen(x_178, x_2);
return x_180;
}
}
case 7:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_204; uint8_t x_205; 
x_188 = lean_ctor_get(x_1, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_189 = x_1;
} else {
 lean_dec_ref(x_1);
 x_189 = lean_box(0);
}
x_204 = lean_unsigned_to_nat(1024u);
x_205 = lean_nat_dec_le(x_204, x_2);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_unsigned_to_nat(2u);
x_207 = lean_nat_to_int(x_206);
x_190 = x_207;
goto block_203;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_to_int(x_208);
x_190 = x_209;
goto block_203;
}
block_203:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_191 = lean_mk_string_unchecked("Lake.CliError.unexpectedArguments", 33, 33);
if (lean_is_scalar(x_189)) {
 x_192 = lean_alloc_ctor(3, 1, 0);
} else {
 x_192 = x_189;
 lean_ctor_set_tag(x_192, 3);
}
lean_ctor_set(x_192, 0, x_191);
x_193 = lean_box(1);
x_194 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_unsigned_to_nat(1024u);
x_196 = l_List_repr_x27___at_____private_Init_Meta_0__Lean_Syntax_reprPreresolved____x40_Init_Meta___hyg_1912__spec__0(x_188, x_195);
x_197 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_200, 0, x_198);
x_201 = lean_unbox(x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_201);
x_202 = l_Repr_addAppParen(x_200, x_2);
return x_202;
}
}
case 8:
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_unsigned_to_nat(1024u);
x_211 = lean_nat_dec_le(x_210, x_2);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_nat_to_int(x_212);
x_30 = x_213;
goto block_38;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_to_int(x_214);
x_30 = x_215;
goto block_38;
}
}
case 9:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_232; uint8_t x_233; 
x_216 = lean_ctor_get(x_1, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_217 = x_1;
} else {
 lean_dec_ref(x_1);
 x_217 = lean_box(0);
}
x_232 = lean_unsigned_to_nat(1024u);
x_233 = lean_nat_dec_le(x_232, x_2);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_unsigned_to_nat(2u);
x_235 = lean_nat_to_int(x_234);
x_218 = x_235;
goto block_231;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_unsigned_to_nat(1u);
x_237 = lean_nat_to_int(x_236);
x_218 = x_237;
goto block_231;
}
block_231:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; 
x_219 = lean_mk_string_unchecked("Lake.CliError.unknownTemplate", 29, 29);
if (lean_is_scalar(x_217)) {
 x_220 = lean_alloc_ctor(3, 1, 0);
} else {
 x_220 = x_217;
 lean_ctor_set_tag(x_220, 3);
}
lean_ctor_set(x_220, 0, x_219);
x_221 = lean_box(1);
x_222 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_String_quote(x_216);
lean_dec(x_216);
x_224 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_226, 0, x_218);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_box(0);
x_228 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_228, 0, x_226);
x_229 = lean_unbox(x_227);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_229);
x_230 = l_Repr_addAppParen(x_228, x_2);
return x_230;
}
}
case 10:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_254; uint8_t x_255; 
x_238 = lean_ctor_get(x_1, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_239 = x_1;
} else {
 lean_dec_ref(x_1);
 x_239 = lean_box(0);
}
x_254 = lean_unsigned_to_nat(1024u);
x_255 = lean_nat_dec_le(x_254, x_2);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_unsigned_to_nat(2u);
x_257 = lean_nat_to_int(x_256);
x_240 = x_257;
goto block_253;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_unsigned_to_nat(1u);
x_259 = lean_nat_to_int(x_258);
x_240 = x_259;
goto block_253;
}
block_253:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
x_241 = lean_mk_string_unchecked("Lake.CliError.unknownConfigLang", 31, 31);
if (lean_is_scalar(x_239)) {
 x_242 = lean_alloc_ctor(3, 1, 0);
} else {
 x_242 = x_239;
 lean_ctor_set_tag(x_242, 3);
}
lean_ctor_set(x_242, 0, x_241);
x_243 = lean_box(1);
x_244 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_String_quote(x_238);
lean_dec(x_238);
x_246 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_248, 0, x_240);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_box(0);
x_250 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_250, 0, x_248);
x_251 = lean_unbox(x_249);
lean_ctor_set_uint8(x_250, sizeof(void*)*1, x_251);
x_252 = l_Repr_addAppParen(x_250, x_2);
return x_252;
}
}
case 11:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_276; uint8_t x_277; 
x_260 = lean_ctor_get(x_1, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_261 = x_1;
} else {
 lean_dec_ref(x_1);
 x_261 = lean_box(0);
}
x_276 = lean_unsigned_to_nat(1024u);
x_277 = lean_nat_dec_le(x_276, x_2);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_unsigned_to_nat(2u);
x_279 = lean_nat_to_int(x_278);
x_262 = x_279;
goto block_275;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_unsigned_to_nat(1u);
x_281 = lean_nat_to_int(x_280);
x_262 = x_281;
goto block_275;
}
block_275:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; 
x_263 = lean_mk_string_unchecked("Lake.CliError.unknownModule", 27, 27);
if (lean_is_scalar(x_261)) {
 x_264 = lean_alloc_ctor(3, 1, 0);
} else {
 x_264 = x_261;
 lean_ctor_set_tag(x_264, 3);
}
lean_ctor_set(x_264, 0, x_263);
x_265 = lean_box(1);
x_266 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_unsigned_to_nat(1024u);
x_268 = l_Lean_Name_reprPrec(x_260, x_267);
x_269 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_272, 0, x_270);
x_273 = lean_unbox(x_271);
lean_ctor_set_uint8(x_272, sizeof(void*)*1, x_273);
x_274 = l_Repr_addAppParen(x_272, x_2);
return x_274;
}
}
case 12:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_303; uint8_t x_304; 
x_282 = lean_ctor_get(x_1, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_283 = x_1;
} else {
 lean_dec_ref(x_1);
 x_283 = lean_box(0);
}
x_303 = lean_unsigned_to_nat(1024u);
x_304 = lean_nat_dec_le(x_303, x_2);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_unsigned_to_nat(2u);
x_306 = lean_nat_to_int(x_305);
x_284 = x_306;
goto block_302;
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_unsigned_to_nat(1u);
x_308 = lean_nat_to_int(x_307);
x_284 = x_308;
goto block_302;
}
block_302:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; 
x_285 = lean_mk_string_unchecked("Lake.CliError.unknownModulePath", 31, 31);
if (lean_is_scalar(x_283)) {
 x_286 = lean_alloc_ctor(3, 1, 0);
} else {
 x_286 = x_283;
 lean_ctor_set_tag(x_286, 3);
}
lean_ctor_set(x_286, 0, x_285);
x_287 = lean_box(1);
x_288 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_unsigned_to_nat(1024u);
x_290 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_291 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = l_String_quote(x_282);
lean_dec(x_282);
x_293 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Repr_addAppParen(x_294, x_289);
x_296 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_296, 0, x_288);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_297, 0, x_284);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_299, 0, x_297);
x_300 = lean_unbox(x_298);
lean_ctor_set_uint8(x_299, sizeof(void*)*1, x_300);
x_301 = l_Repr_addAppParen(x_299, x_2);
return x_301;
}
}
case 13:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_325; uint8_t x_326; 
x_309 = lean_ctor_get(x_1, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_310 = x_1;
} else {
 lean_dec_ref(x_1);
 x_310 = lean_box(0);
}
x_325 = lean_unsigned_to_nat(1024u);
x_326 = lean_nat_dec_le(x_325, x_2);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_unsigned_to_nat(2u);
x_328 = lean_nat_to_int(x_327);
x_311 = x_328;
goto block_324;
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_unsigned_to_nat(1u);
x_330 = lean_nat_to_int(x_329);
x_311 = x_330;
goto block_324;
}
block_324:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; 
x_312 = lean_mk_string_unchecked("Lake.CliError.unknownPackage", 28, 28);
if (lean_is_scalar(x_310)) {
 x_313 = lean_alloc_ctor(3, 1, 0);
} else {
 x_313 = x_310;
 lean_ctor_set_tag(x_313, 3);
}
lean_ctor_set(x_313, 0, x_312);
x_314 = lean_box(1);
x_315 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_String_quote(x_309);
lean_dec(x_309);
x_317 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_319, 0, x_311);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_box(0);
x_321 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_321, 0, x_319);
x_322 = lean_unbox(x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*1, x_322);
x_323 = l_Repr_addAppParen(x_321, x_2);
return x_323;
}
}
case 14:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_352; uint8_t x_353; 
x_331 = lean_ctor_get(x_1, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_1, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_333 = x_1;
} else {
 lean_dec_ref(x_1);
 x_333 = lean_box(0);
}
x_352 = lean_unsigned_to_nat(1024u);
x_353 = lean_nat_dec_le(x_352, x_2);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_unsigned_to_nat(2u);
x_355 = lean_nat_to_int(x_354);
x_334 = x_355;
goto block_351;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_to_int(x_356);
x_334 = x_357;
goto block_351;
}
block_351:
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; 
x_335 = lean_mk_string_unchecked("Lake.CliError.unknownFacet", 26, 26);
x_336 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_336, 0, x_335);
x_337 = lean_box(1);
if (lean_is_scalar(x_333)) {
 x_338 = lean_alloc_ctor(5, 2, 0);
} else {
 x_338 = x_333;
 lean_ctor_set_tag(x_338, 5);
}
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_String_quote(x_331);
lean_dec(x_331);
x_340 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_340, 0, x_339);
x_341 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_337);
x_343 = lean_unsigned_to_nat(1024u);
x_344 = l_Lean_Name_reprPrec(x_332, x_343);
x_345 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_344);
x_346 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_346, 0, x_334);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_box(0);
x_348 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_348, 0, x_346);
x_349 = lean_unbox(x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*1, x_349);
x_350 = l_Repr_addAppParen(x_348, x_2);
return x_350;
}
}
case 15:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_374; uint8_t x_375; 
x_358 = lean_ctor_get(x_1, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_359 = x_1;
} else {
 lean_dec_ref(x_1);
 x_359 = lean_box(0);
}
x_374 = lean_unsigned_to_nat(1024u);
x_375 = lean_nat_dec_le(x_374, x_2);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_unsigned_to_nat(2u);
x_377 = lean_nat_to_int(x_376);
x_360 = x_377;
goto block_373;
}
else
{
lean_object* x_378; lean_object* x_379; 
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_nat_to_int(x_378);
x_360 = x_379;
goto block_373;
}
block_373:
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; 
x_361 = lean_mk_string_unchecked("Lake.CliError.unknownTarget", 27, 27);
if (lean_is_scalar(x_359)) {
 x_362 = lean_alloc_ctor(3, 1, 0);
} else {
 x_362 = x_359;
 lean_ctor_set_tag(x_362, 3);
}
lean_ctor_set(x_362, 0, x_361);
x_363 = lean_box(1);
x_364 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_unsigned_to_nat(1024u);
x_366 = l_Lean_Name_reprPrec(x_358, x_365);
x_367 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_368, 0, x_360);
lean_ctor_set(x_368, 1, x_367);
x_369 = lean_box(0);
x_370 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_370, 0, x_368);
x_371 = lean_unbox(x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*1, x_371);
x_372 = l_Repr_addAppParen(x_370, x_2);
return x_372;
}
}
case 16:
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_400; uint8_t x_401; 
x_380 = lean_ctor_get(x_1, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_1, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_382 = x_1;
} else {
 lean_dec_ref(x_1);
 x_382 = lean_box(0);
}
x_400 = lean_unsigned_to_nat(1024u);
x_401 = lean_nat_dec_le(x_400, x_2);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_unsigned_to_nat(2u);
x_403 = lean_nat_to_int(x_402);
x_383 = x_403;
goto block_399;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_unsigned_to_nat(1u);
x_405 = lean_nat_to_int(x_404);
x_383 = x_405;
goto block_399;
}
block_399:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_384 = lean_mk_string_unchecked("Lake.CliError.missingModule", 27, 27);
x_385 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_385, 0, x_384);
x_386 = lean_box(1);
if (lean_is_scalar(x_382)) {
 x_387 = lean_alloc_ctor(5, 2, 0);
} else {
 x_387 = x_382;
 lean_ctor_set_tag(x_387, 5);
}
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_unsigned_to_nat(1024u);
x_389 = l_Lean_Name_reprPrec(x_380, x_388);
x_390 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_386);
x_392 = l_Lean_Name_reprPrec(x_381, x_388);
x_393 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_394, 0, x_383);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_box(0);
x_396 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_396, 0, x_394);
x_397 = lean_unbox(x_395);
lean_ctor_set_uint8(x_396, sizeof(void*)*1, x_397);
x_398 = l_Repr_addAppParen(x_396, x_2);
return x_398;
}
}
case 17:
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_427; uint8_t x_428; 
x_406 = lean_ctor_get(x_1, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_1, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_408 = x_1;
} else {
 lean_dec_ref(x_1);
 x_408 = lean_box(0);
}
x_427 = lean_unsigned_to_nat(1024u);
x_428 = lean_nat_dec_le(x_427, x_2);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
x_429 = lean_unsigned_to_nat(2u);
x_430 = lean_nat_to_int(x_429);
x_409 = x_430;
goto block_426;
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_unsigned_to_nat(1u);
x_432 = lean_nat_to_int(x_431);
x_409 = x_432;
goto block_426;
}
block_426:
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; 
x_410 = lean_mk_string_unchecked("Lake.CliError.missingTarget", 27, 27);
x_411 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = lean_box(1);
if (lean_is_scalar(x_408)) {
 x_413 = lean_alloc_ctor(5, 2, 0);
} else {
 x_413 = x_408;
 lean_ctor_set_tag(x_413, 5);
}
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = lean_unsigned_to_nat(1024u);
x_415 = l_Lean_Name_reprPrec(x_406, x_414);
x_416 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_415);
x_417 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_412);
x_418 = l_String_quote(x_407);
lean_dec(x_407);
x_419 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_419, 0, x_418);
x_420 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_421, 0, x_409);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_box(0);
x_423 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_423, 0, x_421);
x_424 = lean_unbox(x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*1, x_424);
x_425 = l_Repr_addAppParen(x_423, x_2);
return x_425;
}
}
case 18:
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_449; uint8_t x_450; 
x_433 = lean_ctor_get(x_1, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_434 = x_1;
} else {
 lean_dec_ref(x_1);
 x_434 = lean_box(0);
}
x_449 = lean_unsigned_to_nat(1024u);
x_450 = lean_nat_dec_le(x_449, x_2);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_unsigned_to_nat(2u);
x_452 = lean_nat_to_int(x_451);
x_435 = x_452;
goto block_448;
}
else
{
lean_object* x_453; lean_object* x_454; 
x_453 = lean_unsigned_to_nat(1u);
x_454 = lean_nat_to_int(x_453);
x_435 = x_454;
goto block_448;
}
block_448:
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_436 = lean_mk_string_unchecked("Lake.CliError.invalidBuildTarget", 32, 32);
if (lean_is_scalar(x_434)) {
 x_437 = lean_alloc_ctor(3, 1, 0);
} else {
 x_437 = x_434;
 lean_ctor_set_tag(x_437, 3);
}
lean_ctor_set(x_437, 0, x_436);
x_438 = lean_box(1);
x_439 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
x_440 = l_String_quote(x_433);
lean_dec(x_433);
x_441 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_441, 0, x_440);
x_442 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_441);
x_443 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_box(0);
x_445 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_445, 0, x_443);
x_446 = lean_unbox(x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*1, x_446);
x_447 = l_Repr_addAppParen(x_445, x_2);
return x_447;
}
}
case 19:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_477; uint8_t x_478; 
x_455 = lean_ctor_get(x_1, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_1, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_457 = x_1;
} else {
 lean_dec_ref(x_1);
 x_457 = lean_box(0);
}
x_477 = lean_unsigned_to_nat(1024u);
x_478 = lean_nat_dec_le(x_477, x_2);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_unsigned_to_nat(2u);
x_480 = lean_nat_to_int(x_479);
x_458 = x_480;
goto block_476;
}
else
{
lean_object* x_481; lean_object* x_482; 
x_481 = lean_unsigned_to_nat(1u);
x_482 = lean_nat_to_int(x_481);
x_458 = x_482;
goto block_476;
}
block_476:
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint32_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; lean_object* x_475; 
x_459 = lean_mk_string_unchecked("Lake.CliError.invalidTargetSpec", 31, 31);
x_460 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_460, 0, x_459);
x_461 = lean_box(1);
if (lean_is_scalar(x_457)) {
 x_462 = lean_alloc_ctor(5, 2, 0);
} else {
 x_462 = x_457;
 lean_ctor_set_tag(x_462, 5);
}
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
x_463 = l_String_quote(x_455);
lean_dec(x_455);
x_464 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_464, 0, x_463);
x_465 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_464);
x_466 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_461);
x_467 = lean_unbox_uint32(x_456);
lean_dec(x_456);
x_468 = l_Char_quote(x_467);
x_469 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_469, 0, x_468);
x_470 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_470, 0, x_466);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_471, 0, x_458);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_box(0);
x_473 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_473, 0, x_471);
x_474 = lean_unbox(x_472);
lean_ctor_set_uint8(x_473, sizeof(void*)*1, x_474);
x_475 = l_Repr_addAppParen(x_473, x_2);
return x_475;
}
}
case 20:
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_503; uint8_t x_504; 
x_483 = lean_ctor_get(x_1, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_1, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_485 = x_1;
} else {
 lean_dec_ref(x_1);
 x_485 = lean_box(0);
}
x_503 = lean_unsigned_to_nat(1024u);
x_504 = lean_nat_dec_le(x_503, x_2);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_unsigned_to_nat(2u);
x_506 = lean_nat_to_int(x_505);
x_486 = x_506;
goto block_502;
}
else
{
lean_object* x_507; lean_object* x_508; 
x_507 = lean_unsigned_to_nat(1u);
x_508 = lean_nat_to_int(x_507);
x_486 = x_508;
goto block_502;
}
block_502:
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; 
x_487 = lean_mk_string_unchecked("Lake.CliError.invalidFacet", 26, 26);
x_488 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_488, 0, x_487);
x_489 = lean_box(1);
if (lean_is_scalar(x_485)) {
 x_490 = lean_alloc_ctor(5, 2, 0);
} else {
 x_490 = x_485;
 lean_ctor_set_tag(x_490, 5);
}
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_unsigned_to_nat(1024u);
x_492 = l_Lean_Name_reprPrec(x_483, x_491);
x_493 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_489);
x_495 = l_Lean_Name_reprPrec(x_484, x_491);
x_496 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
x_497 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_497, 0, x_486);
lean_ctor_set(x_497, 1, x_496);
x_498 = lean_box(0);
x_499 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_499, 0, x_497);
x_500 = lean_unbox(x_498);
lean_ctor_set_uint8(x_499, sizeof(void*)*1, x_500);
x_501 = l_Repr_addAppParen(x_499, x_2);
return x_501;
}
}
case 21:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_525; uint8_t x_526; 
x_509 = lean_ctor_get(x_1, 0);
lean_inc(x_509);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_510 = x_1;
} else {
 lean_dec_ref(x_1);
 x_510 = lean_box(0);
}
x_525 = lean_unsigned_to_nat(1024u);
x_526 = lean_nat_dec_le(x_525, x_2);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; 
x_527 = lean_unsigned_to_nat(2u);
x_528 = lean_nat_to_int(x_527);
x_511 = x_528;
goto block_524;
}
else
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_unsigned_to_nat(1u);
x_530 = lean_nat_to_int(x_529);
x_511 = x_530;
goto block_524;
}
block_524:
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; 
x_512 = lean_mk_string_unchecked("Lake.CliError.unknownExe", 24, 24);
if (lean_is_scalar(x_510)) {
 x_513 = lean_alloc_ctor(3, 1, 0);
} else {
 x_513 = x_510;
 lean_ctor_set_tag(x_513, 3);
}
lean_ctor_set(x_513, 0, x_512);
x_514 = lean_box(1);
x_515 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_515, 0, x_513);
lean_ctor_set(x_515, 1, x_514);
x_516 = l_String_quote(x_509);
lean_dec(x_509);
x_517 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_517, 0, x_516);
x_518 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_517);
x_519 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_519, 0, x_511);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_box(0);
x_521 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_521, 0, x_519);
x_522 = lean_unbox(x_520);
lean_ctor_set_uint8(x_521, sizeof(void*)*1, x_522);
x_523 = l_Repr_addAppParen(x_521, x_2);
return x_523;
}
}
case 22:
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_547; uint8_t x_548; 
x_531 = lean_ctor_get(x_1, 0);
lean_inc(x_531);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_532 = x_1;
} else {
 lean_dec_ref(x_1);
 x_532 = lean_box(0);
}
x_547 = lean_unsigned_to_nat(1024u);
x_548 = lean_nat_dec_le(x_547, x_2);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; 
x_549 = lean_unsigned_to_nat(2u);
x_550 = lean_nat_to_int(x_549);
x_533 = x_550;
goto block_546;
}
else
{
lean_object* x_551; lean_object* x_552; 
x_551 = lean_unsigned_to_nat(1u);
x_552 = lean_nat_to_int(x_551);
x_533 = x_552;
goto block_546;
}
block_546:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; 
x_534 = lean_mk_string_unchecked("Lake.CliError.unknownScript", 27, 27);
if (lean_is_scalar(x_532)) {
 x_535 = lean_alloc_ctor(3, 1, 0);
} else {
 x_535 = x_532;
 lean_ctor_set_tag(x_535, 3);
}
lean_ctor_set(x_535, 0, x_534);
x_536 = lean_box(1);
x_537 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
x_538 = l_String_quote(x_531);
lean_dec(x_531);
x_539 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_539, 0, x_538);
x_540 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_539);
x_541 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_541, 0, x_533);
lean_ctor_set(x_541, 1, x_540);
x_542 = lean_box(0);
x_543 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_543, 0, x_541);
x_544 = lean_unbox(x_542);
lean_ctor_set_uint8(x_543, sizeof(void*)*1, x_544);
x_545 = l_Repr_addAppParen(x_543, x_2);
return x_545;
}
}
case 23:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_569; uint8_t x_570; 
x_553 = lean_ctor_get(x_1, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_554 = x_1;
} else {
 lean_dec_ref(x_1);
 x_554 = lean_box(0);
}
x_569 = lean_unsigned_to_nat(1024u);
x_570 = lean_nat_dec_le(x_569, x_2);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_unsigned_to_nat(2u);
x_572 = lean_nat_to_int(x_571);
x_555 = x_572;
goto block_568;
}
else
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_unsigned_to_nat(1u);
x_574 = lean_nat_to_int(x_573);
x_555 = x_574;
goto block_568;
}
block_568:
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; lean_object* x_567; 
x_556 = lean_mk_string_unchecked("Lake.CliError.missingScriptDoc", 30, 30);
if (lean_is_scalar(x_554)) {
 x_557 = lean_alloc_ctor(3, 1, 0);
} else {
 x_557 = x_554;
 lean_ctor_set_tag(x_557, 3);
}
lean_ctor_set(x_557, 0, x_556);
x_558 = lean_box(1);
x_559 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
x_560 = l_String_quote(x_553);
lean_dec(x_553);
x_561 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_561, 0, x_560);
x_562 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_562, 0, x_559);
lean_ctor_set(x_562, 1, x_561);
x_563 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_563, 0, x_555);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_box(0);
x_565 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_565, 0, x_563);
x_566 = lean_unbox(x_564);
lean_ctor_set_uint8(x_565, sizeof(void*)*1, x_566);
x_567 = l_Repr_addAppParen(x_565, x_2);
return x_567;
}
}
case 24:
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_591; uint8_t x_592; 
x_575 = lean_ctor_get(x_1, 0);
lean_inc(x_575);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_576 = x_1;
} else {
 lean_dec_ref(x_1);
 x_576 = lean_box(0);
}
x_591 = lean_unsigned_to_nat(1024u);
x_592 = lean_nat_dec_le(x_591, x_2);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_unsigned_to_nat(2u);
x_594 = lean_nat_to_int(x_593);
x_577 = x_594;
goto block_590;
}
else
{
lean_object* x_595; lean_object* x_596; 
x_595 = lean_unsigned_to_nat(1u);
x_596 = lean_nat_to_int(x_595);
x_577 = x_596;
goto block_590;
}
block_590:
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; lean_object* x_589; 
x_578 = lean_mk_string_unchecked("Lake.CliError.invalidScriptSpec", 31, 31);
if (lean_is_scalar(x_576)) {
 x_579 = lean_alloc_ctor(3, 1, 0);
} else {
 x_579 = x_576;
 lean_ctor_set_tag(x_579, 3);
}
lean_ctor_set(x_579, 0, x_578);
x_580 = lean_box(1);
x_581 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
x_582 = l_String_quote(x_575);
lean_dec(x_575);
x_583 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_583, 0, x_582);
x_584 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_584, 0, x_581);
lean_ctor_set(x_584, 1, x_583);
x_585 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_585, 0, x_577);
lean_ctor_set(x_585, 1, x_584);
x_586 = lean_box(0);
x_587 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_587, 0, x_585);
x_588 = lean_unbox(x_586);
lean_ctor_set_uint8(x_587, sizeof(void*)*1, x_588);
x_589 = l_Repr_addAppParen(x_587, x_2);
return x_589;
}
}
case 25:
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_618; uint8_t x_619; 
x_597 = lean_ctor_get(x_1, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_598 = x_1;
} else {
 lean_dec_ref(x_1);
 x_598 = lean_box(0);
}
x_618 = lean_unsigned_to_nat(1024u);
x_619 = lean_nat_dec_le(x_618, x_2);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; 
x_620 = lean_unsigned_to_nat(2u);
x_621 = lean_nat_to_int(x_620);
x_599 = x_621;
goto block_617;
}
else
{
lean_object* x_622; lean_object* x_623; 
x_622 = lean_unsigned_to_nat(1u);
x_623 = lean_nat_to_int(x_622);
x_599 = x_623;
goto block_617;
}
block_617:
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; lean_object* x_616; 
x_600 = lean_mk_string_unchecked("Lake.CliError.outputConfigExists", 32, 32);
if (lean_is_scalar(x_598)) {
 x_601 = lean_alloc_ctor(3, 1, 0);
} else {
 x_601 = x_598;
 lean_ctor_set_tag(x_601, 3);
}
lean_ctor_set(x_601, 0, x_600);
x_602 = lean_box(1);
x_603 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
x_604 = lean_unsigned_to_nat(1024u);
x_605 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_606 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_606, 0, x_605);
x_607 = l_String_quote(x_597);
lean_dec(x_597);
x_608 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_608, 0, x_607);
x_609 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_608);
x_610 = l_Repr_addAppParen(x_609, x_604);
x_611 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_611, 0, x_603);
lean_ctor_set(x_611, 1, x_610);
x_612 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_612, 0, x_599);
lean_ctor_set(x_612, 1, x_611);
x_613 = lean_box(0);
x_614 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_614, 0, x_612);
x_615 = lean_unbox(x_613);
lean_ctor_set_uint8(x_614, sizeof(void*)*1, x_615);
x_616 = l_Repr_addAppParen(x_614, x_2);
return x_616;
}
}
case 26:
{
lean_object* x_624; uint8_t x_625; 
x_624 = lean_unsigned_to_nat(1024u);
x_625 = lean_nat_dec_le(x_624, x_2);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; 
x_626 = lean_unsigned_to_nat(2u);
x_627 = lean_nat_to_int(x_626);
x_12 = x_627;
goto block_20;
}
else
{
lean_object* x_628; lean_object* x_629; 
x_628 = lean_unsigned_to_nat(1u);
x_629 = lean_nat_to_int(x_628);
x_12 = x_629;
goto block_20;
}
}
case 27:
{
lean_object* x_630; uint8_t x_631; 
x_630 = lean_unsigned_to_nat(1024u);
x_631 = lean_nat_dec_le(x_630, x_2);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_unsigned_to_nat(2u);
x_633 = lean_nat_to_int(x_632);
x_3 = x_633;
goto block_11;
}
else
{
lean_object* x_634; lean_object* x_635; 
x_634 = lean_unsigned_to_nat(1u);
x_635 = lean_nat_to_int(x_634);
x_3 = x_635;
goto block_11;
}
}
case 28:
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_657; uint8_t x_658; 
x_636 = lean_ctor_get(x_1, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_1, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_638 = x_1;
} else {
 lean_dec_ref(x_1);
 x_638 = lean_box(0);
}
x_657 = lean_unsigned_to_nat(1024u);
x_658 = lean_nat_dec_le(x_657, x_2);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_unsigned_to_nat(2u);
x_660 = lean_nat_to_int(x_659);
x_639 = x_660;
goto block_656;
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_unsigned_to_nat(1u);
x_662 = lean_nat_to_int(x_661);
x_639 = x_662;
goto block_656;
}
block_656:
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; lean_object* x_655; 
x_640 = lean_mk_string_unchecked("Lake.CliError.leanRevMismatch", 29, 29);
x_641 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_641, 0, x_640);
x_642 = lean_box(1);
if (lean_is_scalar(x_638)) {
 x_643 = lean_alloc_ctor(5, 2, 0);
} else {
 x_643 = x_638;
 lean_ctor_set_tag(x_643, 5);
}
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
x_644 = l_String_quote(x_636);
lean_dec(x_636);
x_645 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_645, 0, x_644);
x_646 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_642);
x_648 = l_String_quote(x_637);
lean_dec(x_637);
x_649 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_649, 0, x_648);
x_650 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_650, 0, x_647);
lean_ctor_set(x_650, 1, x_649);
x_651 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_651, 0, x_639);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_box(0);
x_653 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_653, 0, x_651);
x_654 = lean_unbox(x_652);
lean_ctor_set_uint8(x_653, sizeof(void*)*1, x_654);
x_655 = l_Repr_addAppParen(x_653, x_2);
return x_655;
}
}
case 29:
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_679; uint8_t x_680; 
x_663 = lean_ctor_get(x_1, 0);
lean_inc(x_663);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_664 = x_1;
} else {
 lean_dec_ref(x_1);
 x_664 = lean_box(0);
}
x_679 = lean_unsigned_to_nat(1024u);
x_680 = lean_nat_dec_le(x_679, x_2);
if (x_680 == 0)
{
lean_object* x_681; lean_object* x_682; 
x_681 = lean_unsigned_to_nat(2u);
x_682 = lean_nat_to_int(x_681);
x_665 = x_682;
goto block_678;
}
else
{
lean_object* x_683; lean_object* x_684; 
x_683 = lean_unsigned_to_nat(1u);
x_684 = lean_nat_to_int(x_683);
x_665 = x_684;
goto block_678;
}
block_678:
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; lean_object* x_677; 
x_666 = lean_mk_string_unchecked("Lake.CliError.invalidEnv", 24, 24);
if (lean_is_scalar(x_664)) {
 x_667 = lean_alloc_ctor(3, 1, 0);
} else {
 x_667 = x_664;
 lean_ctor_set_tag(x_667, 3);
}
lean_ctor_set(x_667, 0, x_666);
x_668 = lean_box(1);
x_669 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
x_670 = l_String_quote(x_663);
lean_dec(x_663);
x_671 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_671, 0, x_670);
x_672 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_671);
x_673 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_673, 0, x_665);
lean_ctor_set(x_673, 1, x_672);
x_674 = lean_box(0);
x_675 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_675, 0, x_673);
x_676 = lean_unbox(x_674);
lean_ctor_set_uint8(x_675, sizeof(void*)*1, x_676);
x_677 = l_Repr_addAppParen(x_675, x_2);
return x_677;
}
}
default: 
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_706; uint8_t x_707; 
x_685 = lean_ctor_get(x_1, 0);
lean_inc(x_685);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_686 = x_1;
} else {
 lean_dec_ref(x_1);
 x_686 = lean_box(0);
}
x_706 = lean_unsigned_to_nat(1024u);
x_707 = lean_nat_dec_le(x_706, x_2);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; 
x_708 = lean_unsigned_to_nat(2u);
x_709 = lean_nat_to_int(x_708);
x_687 = x_709;
goto block_705;
}
else
{
lean_object* x_710; lean_object* x_711; 
x_710 = lean_unsigned_to_nat(1u);
x_711 = lean_nat_to_int(x_710);
x_687 = x_711;
goto block_705;
}
block_705:
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; lean_object* x_704; 
x_688 = lean_mk_string_unchecked("Lake.CliError.missingRootDir", 28, 28);
if (lean_is_scalar(x_686)) {
 x_689 = lean_alloc_ctor(3, 1, 0);
} else {
 x_689 = x_686;
 lean_ctor_set_tag(x_689, 3);
}
lean_ctor_set(x_689, 0, x_688);
x_690 = lean_box(1);
x_691 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
x_692 = lean_unsigned_to_nat(1024u);
x_693 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_694 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_694, 0, x_693);
x_695 = l_String_quote(x_685);
lean_dec(x_685);
x_696 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_696, 0, x_695);
x_697 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_697, 0, x_694);
lean_ctor_set(x_697, 1, x_696);
x_698 = l_Repr_addAppParen(x_697, x_692);
x_699 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_699, 0, x_691);
lean_ctor_set(x_699, 1, x_698);
x_700 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_700, 0, x_687);
lean_ctor_set(x_700, 1, x_699);
x_701 = lean_box(0);
x_702 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_702, 0, x_700);
x_703 = lean_unbox(x_701);
lean_ctor_set_uint8(x_702, sizeof(void*)*1, x_703);
x_704 = l_Repr_addAppParen(x_702, x_2);
return x_704;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lake.CliError.unknownLakeInstall", 32, 32);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lake.CliError.unknownLeanInstall", 32, 32);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lake.CliError.missingCommand", 28, 28);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_mk_string_unchecked("Lake.CliError.unexpectedPlus", 28, 28);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = l_Repr_addAppParen(x_35, x_2);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_324____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_324_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprCliError() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_324____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_CliError_toString___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("missing command", 15, 15);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_mk_string_unchecked("unknown command '", 17, 17);
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = lean_mk_string_unchecked("'", 1, 1);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_mk_string_unchecked("missing ", 8, 8);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("missing ", 8, 8);
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked(" for ", 5, 5);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_11);
lean_dec(x_11);
return x_17;
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("invalid argument for ", 21, 21);
x_21 = lean_string_append(x_20, x_18);
lean_dec(x_18);
x_22 = lean_mk_string_unchecked("; expected ", 11, 11);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_string_append(x_23, x_19);
lean_dec(x_19);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_mk_string_unchecked("unknown short option '-", 23, 23);
x_27 = lean_mk_string_unchecked("", 0, 0);
x_28 = lean_unbox_uint32(x_25);
lean_dec(x_25);
x_29 = lean_string_push(x_27, x_28);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("'", 1, 1);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
return x_32;
}
case 6:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_mk_string_unchecked("unknown long option '", 21, 21);
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = lean_mk_string_unchecked("'", 1, 1);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
return x_37;
}
case 7:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_mk_string_unchecked("unexpected arguments: ", 22, 22);
x_40 = lean_mk_string_unchecked(" ", 1, 1);
x_41 = l_String_intercalate(x_40, x_38);
lean_dec(x_40);
x_42 = lean_string_append(x_39, x_41);
lean_dec(x_41);
return x_42;
}
case 8:
{
lean_object* x_43; 
x_43 = lean_mk_string_unchecked("the `+` option is an Elan feature; rerun Lake via Elan and ensure this option comes first.", 90, 90);
return x_43;
}
case 9:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_mk_string_unchecked("unknown package template `", 26, 26);
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = lean_mk_string_unchecked("`", 1, 1);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
return x_48;
}
case 10:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_mk_string_unchecked("unknown configuration language `", 32, 32);
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = lean_mk_string_unchecked("`", 1, 1);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
return x_53;
}
case 11:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_mk_string_unchecked("unknown module `", 16, 16);
x_56 = lean_box(0);
x_57 = lean_alloc_closure((void*)(l_Lake_CliError_toString___lam__0___boxed), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_unbox(x_56);
x_59 = l_Lean_Name_toString(x_54, x_58, x_57);
x_60 = lean_string_append(x_55, x_59);
lean_dec(x_59);
x_61 = lean_mk_string_unchecked("`", 1, 1);
x_62 = lean_string_append(x_60, x_61);
lean_dec(x_61);
return x_62;
}
case 12:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_mk_string_unchecked("unknown module source path `", 28, 28);
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = lean_mk_string_unchecked("`", 1, 1);
x_67 = lean_string_append(x_65, x_66);
lean_dec(x_66);
return x_67;
}
case 13:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_mk_string_unchecked("unknown package `", 17, 17);
x_70 = lean_string_append(x_69, x_68);
lean_dec(x_68);
x_71 = lean_mk_string_unchecked("`", 1, 1);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
return x_72;
}
case 14:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_mk_string_unchecked("unknown ", 8, 8);
x_76 = lean_string_append(x_75, x_73);
lean_dec(x_73);
x_77 = lean_mk_string_unchecked(" facet `", 8, 8);
x_78 = lean_string_append(x_76, x_77);
lean_dec(x_77);
x_79 = lean_box(0);
x_80 = lean_alloc_closure((void*)(l_Lake_CliError_toString___lam__0___boxed), 2, 1);
lean_closure_set(x_80, 0, x_79);
x_81 = lean_unbox(x_79);
x_82 = l_Lean_Name_toString(x_74, x_81, x_80);
x_83 = lean_string_append(x_78, x_82);
lean_dec(x_82);
x_84 = lean_mk_string_unchecked("`", 1, 1);
x_85 = lean_string_append(x_83, x_84);
lean_dec(x_84);
return x_85;
}
case 15:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_mk_string_unchecked("unknown target `", 16, 16);
x_88 = lean_box(0);
x_89 = lean_alloc_closure((void*)(l_Lake_CliError_toString___lam__0___boxed), 2, 1);
lean_closure_set(x_89, 0, x_88);
x_90 = lean_unbox(x_88);
x_91 = l_Lean_Name_toString(x_86, x_90, x_89);
x_92 = lean_string_append(x_87, x_91);
lean_dec(x_91);
x_93 = lean_mk_string_unchecked("`", 1, 1);
x_94 = lean_string_append(x_92, x_93);
lean_dec(x_93);
return x_94;
}
case 16:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
lean_dec(x_1);
x_97 = lean_mk_string_unchecked("package '", 9, 9);
x_98 = lean_box(0);
x_99 = lean_alloc_closure((void*)(l_Lake_CliError_toString___lam__0___boxed), 2, 1);
lean_closure_set(x_99, 0, x_98);
x_100 = lean_unbox(x_98);
lean_inc(x_99);
x_101 = l_Lean_Name_toString(x_95, x_100, x_99);
x_102 = lean_string_append(x_97, x_101);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked("' has no module '", 17, 17);
x_104 = lean_string_append(x_102, x_103);
lean_dec(x_103);
x_105 = lean_unbox(x_98);
x_106 = l_Lean_Name_toString(x_96, x_105, x_99);
x_107 = lean_string_append(x_104, x_106);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked("'", 1, 1);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
return x_109;
}
case 17:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 1);
lean_inc(x_111);
lean_dec(x_1);
x_112 = lean_mk_string_unchecked("package '", 9, 9);
x_113 = lean_box(0);
x_114 = lean_alloc_closure((void*)(l_Lake_CliError_toString___lam__0___boxed), 2, 1);
lean_closure_set(x_114, 0, x_113);
x_115 = lean_unbox(x_113);
x_116 = l_Lean_Name_toString(x_110, x_115, x_114);
x_117 = lean_string_append(x_112, x_116);
lean_dec(x_116);
x_118 = lean_mk_string_unchecked("' has no target '", 17, 17);
x_119 = lean_string_append(x_117, x_118);
lean_dec(x_118);
x_120 = lean_string_append(x_119, x_111);
lean_dec(x_111);
x_121 = lean_mk_string_unchecked("'", 1, 1);
x_122 = lean_string_append(x_120, x_121);
lean_dec(x_121);
return x_122;
}
case 18:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_1, 0);
lean_inc(x_123);
lean_dec(x_1);
x_124 = lean_mk_string_unchecked("'", 1, 1);
x_125 = lean_string_append(x_124, x_123);
lean_dec(x_123);
x_126 = lean_mk_string_unchecked("' is not a build target (perhaps you meant 'lake query'\?)", 57, 57);
x_127 = lean_string_append(x_125, x_126);
lean_dec(x_126);
return x_127;
}
case 19:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint32_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_1, 1);
lean_inc(x_129);
lean_dec(x_1);
x_130 = lean_mk_string_unchecked("invalid target specifier '", 26, 26);
x_131 = lean_string_append(x_130, x_128);
lean_dec(x_128);
x_132 = lean_mk_string_unchecked("' (too many '", 13, 13);
x_133 = lean_string_append(x_131, x_132);
lean_dec(x_132);
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = lean_unbox_uint32(x_129);
lean_dec(x_129);
x_136 = lean_string_push(x_134, x_135);
x_137 = lean_string_append(x_133, x_136);
lean_dec(x_136);
x_138 = lean_mk_string_unchecked("')", 2, 2);
x_139 = lean_string_append(x_137, x_138);
lean_dec(x_138);
return x_139;
}
case 20:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_140 = lean_ctor_get(x_1, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_1, 1);
lean_inc(x_141);
lean_dec(x_1);
x_142 = lean_mk_string_unchecked("invalid facet `", 15, 15);
x_143 = lean_box(0);
x_144 = lean_alloc_closure((void*)(l_Lake_CliError_toString___lam__0___boxed), 2, 1);
lean_closure_set(x_144, 0, x_143);
x_145 = lean_unbox(x_143);
lean_inc(x_144);
x_146 = l_Lean_Name_toString(x_141, x_145, x_144);
x_147 = lean_string_append(x_142, x_146);
lean_dec(x_146);
x_148 = lean_mk_string_unchecked("`; target ", 10, 10);
x_149 = lean_string_append(x_147, x_148);
lean_dec(x_148);
x_150 = lean_unbox(x_143);
x_151 = l_Lean_Name_toString(x_140, x_150, x_144);
x_152 = lean_string_append(x_149, x_151);
lean_dec(x_151);
x_153 = lean_mk_string_unchecked(" has no facets", 14, 14);
x_154 = lean_string_append(x_152, x_153);
lean_dec(x_153);
return x_154;
}
case 21:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_1, 0);
lean_inc(x_155);
lean_dec(x_1);
x_156 = lean_mk_string_unchecked("unknown executable ", 19, 19);
x_157 = lean_string_append(x_156, x_155);
lean_dec(x_155);
return x_157;
}
case 22:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_1, 0);
lean_inc(x_158);
lean_dec(x_1);
x_159 = lean_mk_string_unchecked("unknown script ", 15, 15);
x_160 = lean_string_append(x_159, x_158);
lean_dec(x_158);
return x_160;
}
case 23:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
lean_dec(x_1);
x_162 = lean_mk_string_unchecked("no documentation provided for `", 31, 31);
x_163 = lean_string_append(x_162, x_161);
lean_dec(x_161);
x_164 = lean_mk_string_unchecked("`", 1, 1);
x_165 = lean_string_append(x_163, x_164);
lean_dec(x_164);
return x_165;
}
case 24:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
lean_dec(x_1);
x_167 = lean_mk_string_unchecked("invalid script specifier '", 26, 26);
x_168 = lean_string_append(x_167, x_166);
lean_dec(x_166);
x_169 = lean_mk_string_unchecked("' (too many '/')", 16, 16);
x_170 = lean_string_append(x_168, x_169);
lean_dec(x_169);
return x_170;
}
case 25:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
lean_dec(x_1);
x_172 = lean_mk_string_unchecked("output configuration file already exists: ", 42, 42);
x_173 = lean_string_append(x_172, x_171);
lean_dec(x_171);
return x_173;
}
case 26:
{
lean_object* x_174; 
x_174 = lean_mk_string_unchecked("could not detect a Lean installation", 36, 36);
return x_174;
}
case 27:
{
lean_object* x_175; 
x_175 = lean_mk_string_unchecked("could not detect the configuration of the Lake installation", 59, 59);
return x_175;
}
case 28:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_176 = lean_ctor_get(x_1, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_1, 1);
lean_inc(x_177);
lean_dec(x_1);
x_178 = lean_mk_string_unchecked("expected Lean commit ", 21, 21);
x_179 = lean_string_append(x_178, x_176);
lean_dec(x_176);
x_180 = lean_mk_string_unchecked(", but got ", 10, 10);
x_181 = lean_string_append(x_179, x_180);
lean_dec(x_180);
x_182 = lean_string_utf8_byte_size(x_177);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_instDecidableEqPos(x_182, x_183);
lean_dec(x_182);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_string_append(x_181, x_177);
lean_dec(x_177);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_177);
x_186 = lean_mk_string_unchecked("nothing", 7, 7);
x_187 = lean_string_append(x_181, x_186);
lean_dec(x_186);
return x_187;
}
}
case 29:
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_1, 0);
lean_inc(x_188);
lean_dec(x_1);
return x_188;
}
default: 
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_1, 0);
lean_inc(x_189);
lean_dec(x_1);
x_190 = lean_mk_string_unchecked("workspace directory not found: ", 31, 31);
x_191 = lean_string_append(x_190, x_189);
lean_dec(x_189);
return x_191;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_toString___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_CliError_toString___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_CliError_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_CliError_toString), 1, 0);
return x_1;
}
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Error(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedCliError = _init_l_Lake_instInhabitedCliError();
lean_mark_persistent(l_Lake_instInhabitedCliError);
l_Lake_instReprCliError = _init_l_Lake_instReprCliError();
lean_mark_persistent(l_Lake_instReprCliError);
l_Lake_CliError_instToString = _init_l_Lake_CliError_instToString();
lean_mark_persistent(l_Lake_CliError_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
