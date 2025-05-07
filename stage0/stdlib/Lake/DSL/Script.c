// Lean compiler output
// Module: Lake.DSL.Script
// Imports: Lake.Config.Package Lake.DSL.Attributes Lake.DSL.Syntax
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandScriptDecl(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandIdentOrStrAsIdent(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lake_DSL_expandAttrs(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandScriptDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_expandScriptDecl__1(lean_object*);
lean_object* l_Lake_DSL_expandOptSimpleBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandScriptDecl___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_expandScriptDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandScriptDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_27 = lean_mk_string_unchecked("Lake", 4, 4);
x_28 = lean_mk_string_unchecked("DSL", 3, 3);
x_29 = lean_mk_string_unchecked("scriptDecl", 10, 10);
lean_inc(x_28);
lean_inc(x_27);
x_30 = l_Lean_Name_mkStr3(x_27, x_28, x_29);
lean_inc(x_1);
x_87 = l_Lean_Syntax_isOfKind(x_1, x_30);
if (x_87 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
x_161 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_162 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_161, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_457; uint8_t x_458; 
x_163 = lean_unsigned_to_nat(0u);
x_457 = l_Lean_Syntax_getArg(x_1, x_163);
x_458 = l_Lean_Syntax_isNone(x_457);
if (x_458 == 0)
{
lean_object* x_459; uint8_t x_460; 
x_459 = lean_unsigned_to_nat(1u);
lean_inc(x_457);
x_460 = l_Lean_Syntax_matchesNull(x_457, x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
lean_dec(x_457);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
x_461 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_462 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_461, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Lean_Syntax_getArg(x_457, x_163);
lean_dec(x_457);
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_463);
x_444 = x_464;
x_445 = x_2;
x_446 = x_3;
goto block_456;
}
}
else
{
lean_object* x_465; 
lean_dec(x_457);
x_465 = lean_box(0);
x_444 = x_465;
x_445 = x_2;
x_446 = x_3;
goto block_456;
}
block_251:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_inc(x_185);
x_187 = l_Array_append(lean_box(0), x_185, x_186);
lean_dec(x_186);
lean_inc(x_177);
lean_inc(x_164);
x_188 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_188, 0, x_164);
lean_ctor_set(x_188, 1, x_177);
lean_ctor_set(x_188, 2, x_187);
x_189 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_178);
lean_inc(x_170);
lean_inc(x_175);
x_190 = l_Lean_Name_mkStr4(x_175, x_170, x_178, x_189);
x_191 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_164);
x_192 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_192, 0, x_164);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_mk_string_unchecked(",", 1, 1);
x_194 = l_Lean_Syntax_TSepArray_ofElems(x_168, x_193, x_182);
lean_dec(x_182);
lean_dec(x_168);
lean_inc(x_185);
x_195 = l_Array_append(lean_box(0), x_185, x_194);
lean_dec(x_194);
lean_inc(x_177);
lean_inc(x_164);
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_164);
lean_ctor_set(x_196, 1, x_177);
lean_ctor_set(x_196, 2, x_195);
x_197 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_164);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_164);
lean_ctor_set(x_198, 1, x_197);
lean_inc(x_164);
x_199 = l_Lean_Syntax_node3(x_164, x_190, x_192, x_196, x_198);
lean_inc(x_177);
lean_inc(x_164);
x_200 = l_Lean_Syntax_node1(x_164, x_177, x_199);
lean_inc(x_185);
lean_inc(x_177);
lean_inc(x_164);
x_201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_201, 0, x_164);
lean_ctor_set(x_201, 1, x_177);
lean_ctor_set(x_201, 2, x_185);
lean_inc_n(x_201, 4);
lean_inc(x_164);
x_202 = l_Lean_Syntax_node6(x_164, x_166, x_188, x_200, x_201, x_201, x_201, x_201);
x_203 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_179);
lean_inc(x_170);
lean_inc(x_175);
x_204 = l_Lean_Name_mkStr4(x_175, x_170, x_179, x_203);
x_205 = lean_mk_string_unchecked("def", 3, 3);
lean_inc(x_164);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_164);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_179);
lean_inc(x_170);
lean_inc(x_175);
x_208 = l_Lean_Name_mkStr4(x_175, x_170, x_179, x_207);
x_209 = l_Lake_DSL_expandIdentOrStrAsIdent(x_165);
x_210 = lean_mk_empty_array_with_capacity(x_163);
x_211 = lean_box(2);
lean_inc(x_177);
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_177);
lean_ctor_set(x_212, 2, x_210);
x_213 = lean_mk_empty_array_with_capacity(x_173);
x_214 = lean_array_push(x_213, x_209);
x_215 = lean_array_push(x_214, x_212);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_211);
lean_ctor_set(x_216, 1, x_208);
lean_ctor_set(x_216, 2, x_215);
x_217 = lean_mk_string_unchecked("optDeclSig", 10, 10);
lean_inc(x_170);
lean_inc(x_175);
x_218 = l_Lean_Name_mkStr4(x_175, x_170, x_179, x_217);
x_219 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_178);
lean_inc(x_170);
lean_inc(x_175);
x_220 = l_Lean_Name_mkStr4(x_175, x_170, x_178, x_219);
x_221 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_164);
x_222 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_222, 0, x_164);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_mk_string_unchecked("ScriptFn", 8, 8);
lean_inc(x_223);
x_224 = l_String_toSubstring_x27(x_223);
lean_inc(x_223);
x_225 = l_Lean_Name_mkStr1(x_223);
x_226 = l_Lean_addMacroScope(x_183, x_225, x_174);
x_227 = l_Lean_Name_mkStr2(x_27, x_223);
x_228 = lean_box(0);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_172);
lean_inc(x_164);
x_231 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_231, 0, x_164);
lean_ctor_set(x_231, 1, x_224);
lean_ctor_set(x_231, 2, x_226);
lean_ctor_set(x_231, 3, x_230);
lean_inc(x_164);
x_232 = l_Lean_Syntax_node2(x_164, x_220, x_222, x_231);
lean_inc(x_177);
lean_inc(x_164);
x_233 = l_Lean_Syntax_node1(x_164, x_177, x_232);
lean_inc(x_201);
lean_inc(x_164);
x_234 = l_Lean_Syntax_node2(x_164, x_218, x_201, x_233);
x_235 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_164);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_164);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_237);
lean_inc(x_178);
lean_inc(x_170);
lean_inc(x_175);
x_238 = l_Lean_Name_mkStr4(x_175, x_170, x_178, x_237);
lean_inc(x_164);
x_239 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_239, 0, x_164);
lean_ctor_set(x_239, 1, x_237);
x_240 = lean_mk_string_unchecked("basicFun", 8, 8);
x_241 = l_Lean_Name_mkStr4(x_175, x_170, x_178, x_240);
lean_inc(x_177);
lean_inc(x_164);
x_242 = l_Lean_Syntax_node1(x_164, x_177, x_171);
x_243 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_164);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_164);
lean_ctor_set(x_244, 1, x_243);
lean_inc(x_201);
lean_inc(x_164);
x_245 = l_Lean_Syntax_node4(x_164, x_241, x_242, x_201, x_244, x_167);
lean_inc(x_164);
x_246 = l_Lean_Syntax_node2(x_164, x_238, x_239, x_245);
lean_inc_n(x_201, 2);
lean_inc(x_164);
x_247 = l_Lean_Syntax_node2(x_164, x_181, x_201, x_201);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_248; 
x_248 = l_Array_empty(lean_box(0));
x_4 = x_164;
x_5 = x_236;
x_6 = x_206;
x_7 = x_234;
x_8 = x_204;
x_9 = x_169;
x_10 = x_176;
x_11 = x_246;
x_12 = x_177;
x_13 = x_216;
x_14 = x_247;
x_15 = x_202;
x_16 = x_184;
x_17 = x_185;
x_18 = x_201;
x_19 = x_248;
goto block_26;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_180, 0);
lean_inc(x_249);
lean_dec(x_180);
x_250 = l_Array_mkArray1___redArg(x_249);
x_4 = x_164;
x_5 = x_236;
x_6 = x_206;
x_7 = x_234;
x_8 = x_204;
x_9 = x_169;
x_10 = x_176;
x_11 = x_246;
x_12 = x_177;
x_13 = x_216;
x_14 = x_247;
x_15 = x_202;
x_16 = x_184;
x_17 = x_185;
x_18 = x_201;
x_19 = x_250;
goto block_26;
}
}
block_343:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_268 = l_Lean_Syntax_getArg(x_1, x_260);
lean_dec(x_1);
x_269 = lean_ctor_get(x_266, 5);
lean_inc(x_269);
x_270 = l_Lean_replaceRef(x_268, x_269);
lean_dec(x_269);
lean_dec(x_268);
x_271 = lean_ctor_get(x_266, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_266, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_266, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_266, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_266, 4);
lean_inc(x_275);
lean_dec(x_266);
lean_inc(x_273);
lean_inc(x_272);
x_276 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_276, 0, x_271);
lean_ctor_set(x_276, 1, x_272);
lean_ctor_set(x_276, 2, x_273);
lean_ctor_set(x_276, 3, x_274);
lean_ctor_set(x_276, 4, x_275);
lean_ctor_set(x_276, 5, x_270);
x_277 = l_Lake_DSL_expandOptSimpleBinder(x_252, x_276, x_267);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Lake_DSL_expandScriptDecl___lam__0(x_276, x_276, x_279);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_SourceInfo_fromRef(x_281, x_259);
lean_dec(x_281);
x_284 = lean_mk_string_unchecked("Term", 4, 4);
x_285 = lean_mk_string_unchecked("attrInstance", 12, 12);
x_286 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_284);
lean_inc(x_254);
lean_inc(x_261);
x_287 = l_Lean_Name_mkStr4(x_261, x_254, x_284, x_286);
x_288 = lean_mk_string_unchecked("null", 4, 4);
x_289 = l_Lean_Name_mkStr1(x_288);
x_290 = l_Array_mkArray0(lean_box(0));
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_283);
x_291 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_291, 0, x_283);
lean_ctor_set(x_291, 1, x_289);
lean_ctor_set(x_291, 2, x_290);
lean_inc(x_291);
lean_inc(x_283);
x_292 = l_Lean_Syntax_node1(x_283, x_287, x_291);
x_293 = lean_mk_string_unchecked("Attr", 4, 4);
x_294 = lean_mk_string_unchecked("simple", 6, 6);
lean_inc(x_254);
lean_inc(x_261);
x_295 = l_Lean_Name_mkStr4(x_261, x_254, x_293, x_294);
x_296 = lean_mk_string_unchecked("«script»", 10, 8);
x_297 = l_String_toSubstring_x27(x_296);
x_298 = lean_mk_string_unchecked("script", 6, 6);
x_299 = l_Lean_Name_mkStr1(x_298);
lean_inc(x_273);
lean_inc(x_272);
x_300 = l_Lean_addMacroScope(x_272, x_299, x_273);
x_301 = lean_box(0);
lean_inc(x_283);
x_302 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_302, 0, x_283);
lean_ctor_set(x_302, 1, x_297);
lean_ctor_set(x_302, 2, x_300);
lean_ctor_set(x_302, 3, x_301);
lean_inc(x_283);
x_303 = l_Lean_Syntax_node2(x_283, x_295, x_302, x_291);
x_304 = l_Lake_DSL_expandScriptDecl___lam__0(x_276, x_276, x_282);
lean_dec(x_276);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_ctor_get(x_304, 1);
x_308 = lean_box(0);
lean_inc(x_284);
lean_inc(x_254);
lean_inc(x_261);
x_309 = l_Lean_Name_mkStr4(x_261, x_254, x_284, x_285);
lean_inc(x_309);
x_310 = l_Lean_Syntax_node2(x_283, x_309, x_292, x_303);
x_311 = lean_mk_empty_array_with_capacity(x_258);
x_312 = l_Lean_Syntax_getArg(x_256, x_163);
lean_dec(x_256);
lean_ctor_set_tag(x_304, 1);
lean_ctor_set(x_304, 1, x_308);
lean_ctor_set(x_304, 0, x_309);
x_313 = lean_array_push(x_311, x_310);
x_314 = l_Lake_DSL_expandAttrs(x_264);
x_315 = l_Array_append(lean_box(0), x_313, x_314);
lean_dec(x_314);
x_316 = l_Lean_SourceInfo_fromRef(x_306, x_259);
lean_dec(x_306);
x_317 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_262);
lean_inc(x_254);
lean_inc(x_261);
x_318 = l_Lean_Name_mkStr4(x_261, x_254, x_262, x_317);
x_319 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_262);
lean_inc(x_254);
lean_inc(x_261);
x_320 = l_Lean_Name_mkStr4(x_261, x_254, x_262, x_319);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_321; 
x_321 = l_Array_empty(lean_box(0));
x_164 = x_316;
x_165 = x_312;
x_166 = x_320;
x_167 = x_253;
x_168 = x_304;
x_169 = x_255;
x_170 = x_254;
x_171 = x_278;
x_172 = x_301;
x_173 = x_260;
x_174 = x_273;
x_175 = x_261;
x_176 = x_307;
x_177 = x_289;
x_178 = x_284;
x_179 = x_262;
x_180 = x_265;
x_181 = x_263;
x_182 = x_315;
x_183 = x_272;
x_184 = x_318;
x_185 = x_290;
x_186 = x_321;
goto block_251;
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_257, 0);
lean_inc(x_322);
lean_dec(x_257);
x_323 = l_Array_mkArray1___redArg(x_322);
x_164 = x_316;
x_165 = x_312;
x_166 = x_320;
x_167 = x_253;
x_168 = x_304;
x_169 = x_255;
x_170 = x_254;
x_171 = x_278;
x_172 = x_301;
x_173 = x_260;
x_174 = x_273;
x_175 = x_261;
x_176 = x_307;
x_177 = x_289;
x_178 = x_284;
x_179 = x_262;
x_180 = x_265;
x_181 = x_263;
x_182 = x_315;
x_183 = x_272;
x_184 = x_318;
x_185 = x_290;
x_186 = x_323;
goto block_251;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_324 = lean_ctor_get(x_304, 0);
x_325 = lean_ctor_get(x_304, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_304);
x_326 = lean_box(0);
lean_inc(x_284);
lean_inc(x_254);
lean_inc(x_261);
x_327 = l_Lean_Name_mkStr4(x_261, x_254, x_284, x_285);
lean_inc(x_327);
x_328 = l_Lean_Syntax_node2(x_283, x_327, x_292, x_303);
x_329 = lean_mk_empty_array_with_capacity(x_258);
x_330 = l_Lean_Syntax_getArg(x_256, x_163);
lean_dec(x_256);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_327);
lean_ctor_set(x_331, 1, x_326);
x_332 = lean_array_push(x_329, x_328);
x_333 = l_Lake_DSL_expandAttrs(x_264);
x_334 = l_Array_append(lean_box(0), x_332, x_333);
lean_dec(x_333);
x_335 = l_Lean_SourceInfo_fromRef(x_324, x_259);
lean_dec(x_324);
x_336 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_262);
lean_inc(x_254);
lean_inc(x_261);
x_337 = l_Lean_Name_mkStr4(x_261, x_254, x_262, x_336);
x_338 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_262);
lean_inc(x_254);
lean_inc(x_261);
x_339 = l_Lean_Name_mkStr4(x_261, x_254, x_262, x_338);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_340; 
x_340 = l_Array_empty(lean_box(0));
x_164 = x_335;
x_165 = x_330;
x_166 = x_339;
x_167 = x_253;
x_168 = x_331;
x_169 = x_255;
x_170 = x_254;
x_171 = x_278;
x_172 = x_301;
x_173 = x_260;
x_174 = x_273;
x_175 = x_261;
x_176 = x_325;
x_177 = x_289;
x_178 = x_284;
x_179 = x_262;
x_180 = x_265;
x_181 = x_263;
x_182 = x_334;
x_183 = x_272;
x_184 = x_337;
x_185 = x_290;
x_186 = x_340;
goto block_251;
}
else
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_257, 0);
lean_inc(x_341);
lean_dec(x_257);
x_342 = l_Array_mkArray1___redArg(x_341);
x_164 = x_335;
x_165 = x_330;
x_166 = x_339;
x_167 = x_253;
x_168 = x_331;
x_169 = x_255;
x_170 = x_254;
x_171 = x_278;
x_172 = x_301;
x_173 = x_260;
x_174 = x_273;
x_175 = x_261;
x_176 = x_325;
x_177 = x_289;
x_178 = x_284;
x_179 = x_262;
x_180 = x_265;
x_181 = x_263;
x_182 = x_334;
x_183 = x_272;
x_184 = x_337;
x_185 = x_290;
x_186 = x_342;
goto block_251;
}
}
}
block_420:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_355 = l_Lean_Syntax_getArg(x_346, x_351);
x_356 = lean_mk_string_unchecked("declValDo", 9, 9);
lean_inc(x_27);
x_357 = l_Lean_Name_mkStr3(x_27, x_28, x_356);
lean_inc(x_355);
x_358 = l_Lean_Syntax_isOfKind(x_355, x_357);
lean_dec(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_30);
x_359 = lean_mk_string_unchecked("Lean", 4, 4);
x_360 = lean_mk_string_unchecked("Parser", 6, 6);
x_361 = lean_mk_string_unchecked("Command", 7, 7);
x_362 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
x_363 = l_Lean_Name_mkStr4(x_359, x_360, x_361, x_362);
lean_inc(x_355);
x_364 = l_Lean_Syntax_isOfKind(x_355, x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_355);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_27);
x_365 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_366 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_365, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_366;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_367 = l_Lean_Syntax_getArg(x_355, x_351);
x_368 = lean_mk_string_unchecked("Termination", 11, 11);
x_369 = lean_mk_string_unchecked("suffix", 6, 6);
lean_inc(x_360);
lean_inc(x_359);
x_370 = l_Lean_Name_mkStr4(x_359, x_360, x_368, x_369);
lean_inc(x_367);
x_371 = l_Lean_Syntax_isOfKind(x_367, x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_370);
lean_dec(x_367);
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_355);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_27);
x_372 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_373 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_372, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_373;
}
else
{
lean_object* x_374; uint8_t x_375; 
x_374 = l_Lean_Syntax_getArg(x_367, x_163);
x_375 = l_Lean_Syntax_matchesNull(x_374, x_163);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; 
lean_dec(x_370);
lean_dec(x_367);
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_355);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_27);
x_376 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_377 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_376, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_377;
}
else
{
lean_object* x_378; uint8_t x_379; 
x_378 = l_Lean_Syntax_getArg(x_367, x_350);
lean_dec(x_367);
x_379 = l_Lean_Syntax_matchesNull(x_378, x_163);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_370);
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_355);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_27);
x_380 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_381 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_380, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_382 = l_Lean_Syntax_getArg(x_355, x_350);
x_383 = l_Lean_Syntax_getArg(x_355, x_344);
lean_dec(x_355);
x_384 = l_Lean_Syntax_isNone(x_383);
if (x_384 == 0)
{
uint8_t x_385; 
lean_inc(x_383);
x_385 = l_Lean_Syntax_matchesNull(x_383, x_350);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_383);
lean_dec(x_382);
lean_dec(x_370);
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_27);
x_386 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_387 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_386, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_388 = l_Lean_Syntax_getArg(x_383, x_163);
lean_dec(x_383);
x_389 = lean_mk_string_unchecked("Term", 4, 4);
x_390 = lean_mk_string_unchecked("whereDecls", 10, 10);
lean_inc(x_360);
lean_inc(x_359);
x_391 = l_Lean_Name_mkStr4(x_359, x_360, x_389, x_390);
lean_inc(x_388);
x_392 = l_Lean_Syntax_isOfKind(x_388, x_391);
lean_dec(x_391);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_388);
lean_dec(x_382);
lean_dec(x_370);
lean_dec(x_363);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_27);
x_393 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_394 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_393, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_388);
x_252 = x_352;
x_253 = x_382;
x_254 = x_360;
x_255 = x_363;
x_256 = x_346;
x_257 = x_347;
x_258 = x_350;
x_259 = x_358;
x_260 = x_351;
x_261 = x_359;
x_262 = x_361;
x_263 = x_370;
x_264 = x_349;
x_265 = x_395;
x_266 = x_353;
x_267 = x_354;
goto block_343;
}
}
}
else
{
lean_object* x_396; 
lean_dec(x_383);
x_396 = lean_box(0);
x_252 = x_352;
x_253 = x_382;
x_254 = x_360;
x_255 = x_363;
x_256 = x_346;
x_257 = x_347;
x_258 = x_350;
x_259 = x_358;
x_260 = x_351;
x_261 = x_359;
x_262 = x_361;
x_263 = x_370;
x_264 = x_349;
x_265 = x_396;
x_266 = x_353;
x_267 = x_354;
goto block_343;
}
}
}
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
lean_dec(x_346);
lean_dec(x_27);
x_397 = l_Lean_Syntax_getArg(x_355, x_163);
x_398 = lean_mk_string_unchecked("Lean", 4, 4);
x_399 = lean_mk_string_unchecked("Parser", 6, 6);
x_400 = lean_mk_string_unchecked("Term", 4, 4);
x_401 = lean_mk_string_unchecked("do", 2, 2);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_402 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_401);
lean_inc(x_397);
x_403 = l_Lean_Syntax_isOfKind(x_397, x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_355);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_30);
x_404 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_405 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_404, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_406 = l_Lean_Syntax_getArg(x_397, x_350);
lean_dec(x_397);
x_407 = l_Lean_Syntax_getArg(x_355, x_350);
lean_dec(x_355);
x_408 = l_Lean_Syntax_isNone(x_407);
if (x_408 == 0)
{
uint8_t x_409; 
lean_inc(x_407);
x_409 = l_Lean_Syntax_matchesNull(x_407, x_350);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_30);
x_410 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_411 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_410, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = l_Lean_Syntax_getArg(x_407, x_163);
lean_dec(x_407);
x_413 = lean_mk_string_unchecked("whereDecls", 10, 10);
lean_inc(x_399);
lean_inc(x_398);
x_414 = l_Lean_Name_mkStr4(x_398, x_399, x_400, x_413);
lean_inc(x_412);
x_415 = l_Lean_Syntax_isOfKind(x_412, x_414);
lean_dec(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; 
lean_dec(x_412);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_30);
x_416 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_417 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_416, x_353, x_354);
lean_dec(x_353);
lean_dec(x_1);
return x_417;
}
else
{
lean_object* x_418; 
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_412);
x_135 = x_402;
x_136 = x_352;
x_137 = x_345;
x_138 = x_399;
x_139 = x_401;
x_140 = x_406;
x_141 = x_398;
x_142 = x_347;
x_143 = x_349;
x_144 = x_348;
x_145 = x_351;
x_146 = x_418;
x_147 = x_353;
x_148 = x_354;
goto block_160;
}
}
}
else
{
lean_object* x_419; 
lean_dec(x_407);
lean_dec(x_400);
x_419 = lean_box(0);
x_135 = x_402;
x_136 = x_352;
x_137 = x_345;
x_138 = x_399;
x_139 = x_401;
x_140 = x_406;
x_141 = x_398;
x_142 = x_347;
x_143 = x_349;
x_144 = x_348;
x_145 = x_351;
x_146 = x_419;
x_147 = x_353;
x_148 = x_354;
goto block_160;
}
}
}
}
block_443:
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; 
x_426 = lean_unsigned_to_nat(3u);
x_427 = l_Lean_Syntax_getArg(x_1, x_426);
x_428 = lean_mk_string_unchecked("scriptDeclSpec", 14, 14);
lean_inc(x_28);
lean_inc(x_27);
x_429 = l_Lean_Name_mkStr3(x_27, x_28, x_428);
lean_inc(x_427);
x_430 = l_Lean_Syntax_isOfKind(x_427, x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_429);
lean_dec(x_427);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
x_431 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_432 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_431, x_424, x_425);
lean_dec(x_424);
lean_dec(x_1);
return x_432;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
x_433 = lean_unsigned_to_nat(2u);
x_434 = l_Lean_Syntax_getArg(x_427, x_163);
x_435 = l_Lean_Syntax_getArg(x_427, x_422);
x_436 = l_Lean_Syntax_isNone(x_435);
if (x_436 == 0)
{
uint8_t x_437; 
lean_inc(x_435);
x_437 = l_Lean_Syntax_matchesNull(x_435, x_422);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_429);
lean_dec(x_427);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
x_438 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_439 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_438, x_424, x_425);
lean_dec(x_424);
lean_dec(x_1);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; 
x_440 = l_Lean_Syntax_getArg(x_435, x_163);
lean_dec(x_435);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_440);
x_344 = x_426;
x_345 = x_434;
x_346 = x_427;
x_347 = x_421;
x_348 = x_429;
x_349 = x_423;
x_350 = x_422;
x_351 = x_433;
x_352 = x_441;
x_353 = x_424;
x_354 = x_425;
goto block_420;
}
}
else
{
lean_object* x_442; 
lean_dec(x_435);
x_442 = lean_box(0);
x_344 = x_426;
x_345 = x_434;
x_346 = x_427;
x_347 = x_421;
x_348 = x_429;
x_349 = x_423;
x_350 = x_422;
x_351 = x_433;
x_352 = x_442;
x_353 = x_424;
x_354 = x_425;
goto block_420;
}
}
}
block_456:
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_447 = lean_unsigned_to_nat(1u);
x_448 = l_Lean_Syntax_getArg(x_1, x_447);
x_449 = l_Lean_Syntax_isNone(x_448);
if (x_449 == 0)
{
uint8_t x_450; 
lean_inc(x_448);
x_450 = l_Lean_Syntax_matchesNull(x_448, x_447);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_448);
lean_dec(x_444);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
x_451 = lean_mk_string_unchecked("ill-formed script declaration", 29, 29);
x_452 = l_Lean_Macro_throwErrorAt(lean_box(0), x_1, x_451, x_445, x_446);
lean_dec(x_445);
lean_dec(x_1);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; 
x_453 = l_Lean_Syntax_getArg(x_448, x_163);
lean_dec(x_448);
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_453);
x_421 = x_444;
x_422 = x_447;
x_423 = x_454;
x_424 = x_445;
x_425 = x_446;
goto block_443;
}
}
else
{
lean_object* x_455; 
lean_dec(x_448);
x_455 = lean_box(0);
x_421 = x_444;
x_422 = x_447;
x_423 = x_455;
x_424 = x_445;
x_425 = x_446;
goto block_443;
}
}
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Array_append(lean_box(0), x_17, x_19);
lean_dec(x_19);
lean_inc(x_4);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_20);
lean_inc(x_4);
x_22 = l_Lean_Syntax_node4(x_4, x_9, x_5, x_11, x_14, x_21);
lean_inc(x_4);
x_23 = l_Lean_Syntax_node5(x_4, x_8, x_6, x_13, x_7, x_22, x_18);
x_24 = l_Lean_Syntax_node2(x_4, x_16, x_15, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
block_52:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Array_append(lean_box(0), x_31, x_45);
lean_dec(x_45);
lean_inc(x_35);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
lean_inc(x_35);
x_48 = l_Lean_Syntax_node4(x_35, x_40, x_37, x_38, x_34, x_47);
lean_inc(x_35);
x_49 = l_Lean_Syntax_node3(x_35, x_36, x_39, x_32, x_48);
x_50 = l_Lean_Syntax_node4(x_35, x_30, x_33, x_41, x_43, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
block_86:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_53);
x_69 = l_Array_append(lean_box(0), x_53, x_68);
lean_dec(x_68);
lean_inc(x_67);
lean_inc(x_57);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_mk_string_unchecked("Command", 7, 7);
x_72 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_56);
lean_inc(x_63);
x_73 = l_Lean_Name_mkStr4(x_63, x_56, x_71, x_72);
x_74 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_57);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_57);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_57);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_61);
lean_inc(x_57);
x_77 = l_Lean_Syntax_node2(x_57, x_54, x_76, x_62);
x_78 = lean_mk_string_unchecked("Termination", 11, 11);
x_79 = lean_mk_string_unchecked("suffix", 6, 6);
x_80 = l_Lean_Name_mkStr4(x_63, x_56, x_78, x_79);
lean_inc(x_53);
lean_inc(x_67);
lean_inc(x_57);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_57);
lean_ctor_set(x_81, 1, x_67);
lean_ctor_set(x_81, 2, x_53);
lean_inc(x_81);
lean_inc(x_57);
x_82 = l_Lean_Syntax_node2(x_57, x_80, x_81, x_81);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_83; 
x_83 = l_Array_empty(lean_box(0));
x_31 = x_53;
x_32 = x_70;
x_33 = x_55;
x_34 = x_82;
x_35 = x_57;
x_36 = x_59;
x_37 = x_75;
x_38 = x_77;
x_39 = x_60;
x_40 = x_73;
x_41 = x_64;
x_42 = x_66;
x_43 = x_65;
x_44 = x_67;
x_45 = x_83;
goto block_52;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_58, 0);
lean_inc(x_84);
lean_dec(x_58);
x_85 = l_Array_mkArray1___redArg(x_84);
x_31 = x_53;
x_32 = x_70;
x_33 = x_55;
x_34 = x_82;
x_35 = x_57;
x_36 = x_59;
x_37 = x_75;
x_38 = x_77;
x_39 = x_60;
x_40 = x_73;
x_41 = x_64;
x_42 = x_66;
x_43 = x_65;
x_44 = x_67;
x_45 = x_85;
goto block_52;
}
}
block_112:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_inc(x_89);
x_104 = l_Array_append(lean_box(0), x_89, x_103);
lean_dec(x_103);
lean_inc(x_102);
lean_inc(x_93);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_105, 2, x_104);
x_106 = l_Lean_SourceInfo_fromRef(x_100, x_87);
lean_dec(x_100);
x_107 = lean_mk_string_unchecked("script", 6, 6);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_109; 
x_109 = l_Array_empty(lean_box(0));
x_53 = x_89;
x_54 = x_90;
x_55 = x_91;
x_56 = x_92;
x_57 = x_93;
x_58 = x_94;
x_59 = x_95;
x_60 = x_96;
x_61 = x_97;
x_62 = x_98;
x_63 = x_99;
x_64 = x_105;
x_65 = x_108;
x_66 = x_101;
x_67 = x_102;
x_68 = x_109;
goto block_86;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_88, 0);
lean_inc(x_110);
lean_dec(x_88);
x_111 = l_Array_mkArray1___redArg(x_110);
x_53 = x_89;
x_54 = x_90;
x_55 = x_91;
x_56 = x_92;
x_57 = x_93;
x_58 = x_94;
x_59 = x_95;
x_60 = x_96;
x_61 = x_97;
x_62 = x_98;
x_63 = x_99;
x_64 = x_105;
x_65 = x_108;
x_66 = x_101;
x_67 = x_102;
x_68 = x_111;
goto block_86;
}
}
block_134:
{
lean_object* x_129; lean_object* x_130; 
lean_inc(x_113);
x_129 = l_Array_append(lean_box(0), x_113, x_128);
lean_dec(x_128);
lean_inc(x_127);
lean_inc(x_117);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_117);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_131; 
x_131 = l_Array_empty(lean_box(0));
x_88 = x_114;
x_89 = x_113;
x_90 = x_115;
x_91 = x_130;
x_92 = x_116;
x_93 = x_117;
x_94 = x_118;
x_95 = x_119;
x_96 = x_120;
x_97 = x_121;
x_98 = x_122;
x_99 = x_123;
x_100 = x_124;
x_101 = x_126;
x_102 = x_127;
x_103 = x_131;
goto block_112;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
lean_dec(x_125);
x_133 = l_Array_mkArray1___redArg(x_132);
x_88 = x_114;
x_89 = x_113;
x_90 = x_115;
x_91 = x_130;
x_92 = x_116;
x_93 = x_117;
x_94 = x_118;
x_95 = x_119;
x_96 = x_120;
x_97 = x_121;
x_98 = x_122;
x_99 = x_123;
x_100 = x_124;
x_101 = x_126;
x_102 = x_127;
x_103 = x_133;
goto block_112;
}
}
block_160:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_149 = l_Lean_Syntax_getArg(x_1, x_145);
lean_dec(x_1);
x_150 = lean_ctor_get(x_147, 5);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_box(0);
x_152 = lean_unbox(x_151);
x_153 = l_Lean_SourceInfo_fromRef(x_150, x_152);
lean_dec(x_150);
x_154 = lean_mk_string_unchecked("null", 4, 4);
x_155 = l_Lean_Name_mkStr1(x_154);
x_156 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_157; 
x_157 = l_Array_empty(lean_box(0));
x_113 = x_156;
x_114 = x_136;
x_115 = x_135;
x_116 = x_138;
x_117 = x_153;
x_118 = x_146;
x_119 = x_144;
x_120 = x_137;
x_121 = x_139;
x_122 = x_140;
x_123 = x_141;
x_124 = x_149;
x_125 = x_143;
x_126 = x_148;
x_127 = x_155;
x_128 = x_157;
goto block_134;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_142, 0);
lean_inc(x_158);
lean_dec(x_142);
x_159 = l_Array_mkArray1___redArg(x_158);
x_113 = x_156;
x_114 = x_136;
x_115 = x_135;
x_116 = x_138;
x_117 = x_153;
x_118 = x_146;
x_119 = x_144;
x_120 = x_137;
x_121 = x_139;
x_122 = x_140;
x_123 = x_141;
x_124 = x_149;
x_125 = x_143;
x_126 = x_148;
x_127 = x_155;
x_128 = x_159;
goto block_134;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DSL_expandScriptDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_DSL_expandScriptDecl___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lake_DSL_expandScriptDecl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lake", 4, 4);
x_4 = lean_mk_string_unchecked("DSL", 3, 3);
x_5 = lean_mk_string_unchecked("scriptDecl", 10, 10);
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("expandScriptDecl", 16, 16);
x_8 = l_Lean_Name_mkStr3(x_3, x_4, x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_DSL_expandScriptDecl), 3, 0);
x_10 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_8, x_9, x_1);
return x_10;
}
}
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Attributes(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Script(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_DSL_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lake_DSL_expandScriptDecl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
