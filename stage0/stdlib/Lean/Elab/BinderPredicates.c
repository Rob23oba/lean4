// Lean compiler output
// Module: Lean.Elab.BinderPredicates
// Imports: Init.BinderPredicates Lean.Parser.Syntax Lean.Elab.MacroArgUtil Lean.Linter.MissingDocs
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
lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabBinderPred_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabBinderPred_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkBinderPredicate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkBinderPredicate(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_lint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabBinderPred__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabBinderPred(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabBinderPred_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_3, x_2);
lean_inc(x_4);
x_10 = l_Lean_Elab_Command_expandMacroArg(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_14, x_2, x_11);
x_2 = x_17;
x_3 = x_18;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabBinderPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; size_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; size_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("Command", 7, 7);
x_8 = lean_mk_string_unchecked("binderPredicate", 15, 15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_223; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_223 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_361; uint8_t x_362; 
x_224 = lean_unsigned_to_nat(0u);
x_361 = l_Lean_Syntax_getArg(x_1, x_224);
x_362 = l_Lean_Syntax_isNone(x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; 
x_363 = lean_unsigned_to_nat(1u);
lean_inc(x_361);
x_364 = l_Lean_Syntax_matchesNull(x_361, x_363);
if (x_364 == 0)
{
lean_object* x_365; 
lean_dec(x_361);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_365 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_366 = l_Lean_Syntax_getArg(x_361, x_224);
lean_dec(x_361);
x_367 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_368 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_367);
lean_inc(x_366);
x_369 = l_Lean_Syntax_isOfKind(x_366, x_368);
lean_dec(x_368);
if (x_369 == 0)
{
lean_object* x_370; 
lean_dec(x_366);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_370 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_370;
}
else
{
lean_object* x_371; 
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_366);
x_341 = x_371;
x_342 = x_2;
x_343 = x_3;
x_344 = x_4;
goto block_360;
}
}
}
else
{
lean_object* x_372; 
lean_dec(x_361);
x_372 = lean_box(0);
x_341 = x_372;
x_342 = x_2;
x_343 = x_3;
x_344 = x_4;
goto block_360;
}
block_284:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_unsigned_to_nat(7u);
x_237 = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(x_237, 0, x_232);
x_238 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_237, x_233, x_234, x_235);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; size_t x_243; size_t x_244; lean_object* x_245; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Syntax_getArg(x_1, x_236);
x_242 = l_Lean_Syntax_getArgs(x_241);
lean_dec(x_241);
x_243 = lean_array_size(x_242);
x_244 = lean_usize_of_nat(x_224);
lean_inc(x_233);
x_245 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabBinderPred_spec__0(x_243, x_244, x_242, x_233, x_234, x_240);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Array_unzip___redArg(x_246);
lean_dec(x_246);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_unsigned_to_nat(6u);
x_252 = lean_unsigned_to_nat(9u);
x_253 = lean_mk_string_unchecked("term", 4, 4);
x_254 = l_Lean_Syntax_getArg(x_1, x_251);
x_255 = l_Lean_Syntax_getArg(x_1, x_252);
x_256 = l_Lean_Syntax_getArg(x_1, x_226);
lean_dec(x_1);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_257 = lean_mk_string_unchecked("binderTerm", 10, 10);
x_258 = l_Lean_Name_mkStr1(x_257);
x_259 = lean_mk_string_unchecked("null", 4, 4);
x_260 = l_Lean_Name_mkStr1(x_259);
x_261 = lean_box(2);
lean_inc(x_249);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
lean_ctor_set(x_262, 2, x_249);
x_263 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkNameFromParserSyntax___boxed), 4, 2);
lean_closure_set(x_263, 0, x_258);
lean_closure_set(x_263, 1, x_262);
x_264 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_263, x_233, x_234, x_247);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_box(0);
x_268 = lean_unbox(x_267);
lean_inc(x_265);
x_269 = l_Lean_mkIdentFrom(x_256, x_265, x_268);
x_175 = x_234;
x_176 = x_225;
x_177 = x_249;
x_178 = x_228;
x_179 = x_250;
x_180 = x_244;
x_181 = x_254;
x_182 = x_255;
x_183 = x_229;
x_184 = x_265;
x_185 = x_239;
x_186 = x_227;
x_187 = x_253;
x_188 = x_256;
x_189 = x_266;
x_190 = x_231;
x_191 = x_233;
x_192 = x_269;
goto block_222;
}
else
{
uint8_t x_270; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_270 = !lean_is_exclusive(x_264);
if (x_270 == 0)
{
return x_264;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_264, 0);
x_272 = lean_ctor_get(x_264, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_264);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_230, 0);
lean_inc(x_274);
lean_dec(x_230);
x_275 = l_Lean_Syntax_getId(x_274);
x_175 = x_234;
x_176 = x_225;
x_177 = x_249;
x_178 = x_228;
x_179 = x_250;
x_180 = x_244;
x_181 = x_254;
x_182 = x_255;
x_183 = x_229;
x_184 = x_275;
x_185 = x_239;
x_186 = x_227;
x_187 = x_253;
x_188 = x_256;
x_189 = x_247;
x_190 = x_231;
x_191 = x_233;
x_192 = x_274;
goto block_222;
}
}
else
{
uint8_t x_276; 
lean_dec(x_239);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_245);
if (x_276 == 0)
{
return x_245;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_245, 0);
x_278 = lean_ctor_get(x_245, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_245);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_225);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_280 = !lean_is_exclusive(x_238);
if (x_280 == 0)
{
return x_238;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_238, 0);
x_282 = lean_ctor_get(x_238, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_238);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
block_309:
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_296 = lean_unsigned_to_nat(5u);
x_297 = l_Lean_Syntax_getArg(x_1, x_296);
x_298 = l_Lean_Syntax_isNone(x_297);
if (x_298 == 0)
{
uint8_t x_299; 
lean_inc(x_297);
x_299 = l_Lean_Syntax_matchesNull(x_297, x_285);
if (x_299 == 0)
{
lean_object* x_300; 
lean_dec(x_297);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_300 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_293, x_294, x_295);
lean_dec(x_294);
lean_dec(x_293);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = l_Lean_Syntax_getArg(x_297, x_224);
lean_dec(x_297);
x_302 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_303 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_302);
lean_inc(x_301);
x_304 = l_Lean_Syntax_isOfKind(x_301, x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; 
lean_dec(x_301);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_305 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_293, x_294, x_295);
lean_dec(x_294);
lean_dec(x_293);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; 
x_306 = l_Lean_Syntax_getArg(x_301, x_286);
lean_dec(x_301);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_225 = x_287;
x_226 = x_286;
x_227 = x_289;
x_228 = x_288;
x_229 = x_290;
x_230 = x_292;
x_231 = x_291;
x_232 = x_307;
x_233 = x_293;
x_234 = x_294;
x_235 = x_295;
goto block_284;
}
}
}
else
{
lean_object* x_308; 
lean_dec(x_297);
x_308 = lean_box(0);
x_225 = x_287;
x_226 = x_286;
x_227 = x_289;
x_228 = x_288;
x_229 = x_290;
x_230 = x_292;
x_231 = x_291;
x_232 = x_308;
x_233 = x_293;
x_234 = x_294;
x_235 = x_295;
goto block_284;
}
}
block_340:
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_unsigned_to_nat(2u);
x_317 = l_Lean_Syntax_getArg(x_1, x_316);
lean_inc(x_317);
x_318 = l_Lean_Syntax_matchesNull(x_317, x_310);
if (x_318 == 0)
{
lean_object* x_319; 
lean_dec(x_317);
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_319 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_313, x_314, x_315);
lean_dec(x_314);
lean_dec(x_313);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_320 = l_Lean_Syntax_getArg(x_317, x_224);
lean_dec(x_317);
x_321 = lean_mk_string_unchecked("Term", 4, 4);
x_322 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_321);
lean_inc(x_6);
lean_inc(x_5);
x_323 = l_Lean_Name_mkStr4(x_5, x_6, x_321, x_322);
lean_inc(x_320);
x_324 = l_Lean_Syntax_isOfKind(x_320, x_323);
if (x_324 == 0)
{
lean_object* x_325; 
lean_dec(x_323);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_325 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_313, x_314, x_315);
lean_dec(x_314);
lean_dec(x_313);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_326 = lean_unsigned_to_nat(3u);
x_327 = lean_unsigned_to_nat(4u);
x_328 = l_Lean_Syntax_getArg(x_1, x_327);
x_329 = l_Lean_Syntax_isNone(x_328);
if (x_329 == 0)
{
uint8_t x_330; 
lean_inc(x_328);
x_330 = l_Lean_Syntax_matchesNull(x_328, x_310);
if (x_330 == 0)
{
lean_object* x_331; 
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_331 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_313, x_314, x_315);
lean_dec(x_314);
lean_dec(x_313);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_332 = l_Lean_Syntax_getArg(x_328, x_224);
lean_dec(x_328);
x_333 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_334 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_333);
lean_inc(x_332);
x_335 = l_Lean_Syntax_isOfKind(x_332, x_334);
lean_dec(x_334);
if (x_335 == 0)
{
lean_object* x_336; 
lean_dec(x_332);
lean_dec(x_323);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_336 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_313, x_314, x_315);
lean_dec(x_314);
lean_dec(x_313);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = l_Lean_Syntax_getArg(x_332, x_326);
lean_dec(x_332);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_337);
x_285 = x_310;
x_286 = x_326;
x_287 = x_312;
x_288 = x_323;
x_289 = x_311;
x_290 = x_320;
x_291 = x_321;
x_292 = x_338;
x_293 = x_313;
x_294 = x_314;
x_295 = x_315;
goto block_309;
}
}
}
else
{
lean_object* x_339; 
lean_dec(x_328);
x_339 = lean_box(0);
x_285 = x_310;
x_286 = x_326;
x_287 = x_312;
x_288 = x_323;
x_289 = x_311;
x_290 = x_320;
x_291 = x_321;
x_292 = x_339;
x_293 = x_313;
x_294 = x_314;
x_295 = x_315;
goto block_309;
}
}
}
}
block_360:
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_345 = lean_unsigned_to_nat(1u);
x_346 = l_Lean_Syntax_getArg(x_1, x_345);
x_347 = l_Lean_Syntax_isNone(x_346);
if (x_347 == 0)
{
uint8_t x_348; 
lean_inc(x_346);
x_348 = l_Lean_Syntax_matchesNull(x_346, x_345);
if (x_348 == 0)
{
lean_object* x_349; 
lean_dec(x_346);
lean_dec(x_341);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_349 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_342, x_343, x_344);
lean_dec(x_343);
lean_dec(x_342);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_350 = l_Lean_Syntax_getArg(x_346, x_224);
lean_dec(x_346);
x_351 = lean_mk_string_unchecked("Term", 4, 4);
x_352 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
x_353 = l_Lean_Name_mkStr4(x_5, x_6, x_351, x_352);
lean_inc(x_350);
x_354 = l_Lean_Syntax_isOfKind(x_350, x_353);
lean_dec(x_353);
if (x_354 == 0)
{
lean_object* x_355; 
lean_dec(x_350);
lean_dec(x_341);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_355 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_342, x_343, x_344);
lean_dec(x_343);
lean_dec(x_342);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = l_Lean_Syntax_getArg(x_350, x_345);
lean_dec(x_350);
x_357 = l_Lean_Syntax_getArgs(x_356);
lean_dec(x_356);
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_357);
x_310 = x_345;
x_311 = x_341;
x_312 = x_358;
x_313 = x_342;
x_314 = x_343;
x_315 = x_344;
goto block_340;
}
}
}
else
{
lean_object* x_359; 
lean_dec(x_346);
x_359 = lean_box(0);
x_310 = x_345;
x_311 = x_341;
x_312 = x_359;
x_313 = x_342;
x_314 = x_343;
x_315 = x_344;
goto block_340;
}
}
}
block_132:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_17);
x_38 = l_Array_append(lean_box(0), x_17, x_37);
lean_dec(x_37);
lean_inc(x_16);
lean_inc(x_15);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_16);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_SourceInfo_fromRef(x_35, x_10);
lean_dec(x_35);
lean_inc(x_40);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_16);
lean_ctor_set(x_42, 2, x_17);
x_43 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_43);
x_45 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_15);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_15);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_15);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_15);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_15);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_52);
lean_inc(x_50);
lean_inc(x_46);
lean_inc(x_15);
x_53 = l_Lean_Syntax_node5(x_15, x_44, x_46, x_48, x_50, x_33, x_52);
lean_inc(x_16);
lean_inc(x_15);
x_54 = l_Lean_Syntax_node1(x_15, x_16, x_53);
x_55 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_55);
x_57 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_15);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_15);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_60 = l_Lean_Syntax_mkNumLit(x_59, x_24);
lean_inc(x_52);
lean_inc(x_46);
lean_inc(x_15);
x_61 = l_Lean_Syntax_node5(x_15, x_56, x_46, x_58, x_50, x_60, x_52);
lean_inc(x_16);
lean_inc(x_15);
x_62 = l_Lean_Syntax_node1(x_15, x_16, x_61);
x_63 = lean_array_size(x_13);
x_64 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_63, x_27, x_13);
x_65 = l_Array_append(lean_box(0), x_17, x_64);
lean_dec(x_64);
lean_inc(x_16);
lean_inc(x_15);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_15);
lean_ctor_set(x_66, 1, x_16);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_15);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_15);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_31);
x_69 = l_String_toSubstring_x27(x_31);
x_70 = l_Lean_addMacroScope(x_21, x_22, x_20);
lean_inc(x_5);
x_71 = l_Lean_Name_mkStr2(x_5, x_31);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_15);
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_15);
lean_ctor_set(x_75, 1, x_69);
lean_ctor_set(x_75, 2, x_70);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_unsigned_to_nat(10u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
lean_inc(x_28);
x_78 = lean_array_push(x_77, x_28);
x_79 = lean_array_push(x_78, x_39);
x_80 = lean_array_push(x_79, x_18);
x_81 = lean_array_push(x_80, x_41);
lean_inc(x_42);
x_82 = lean_array_push(x_81, x_42);
x_83 = lean_array_push(x_82, x_54);
x_84 = lean_array_push(x_83, x_62);
x_85 = lean_array_push(x_84, x_66);
lean_inc(x_68);
x_86 = lean_array_push(x_85, x_68);
x_87 = lean_array_push(x_86, x_75);
lean_inc(x_15);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_15);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_89);
lean_inc(x_6);
lean_inc(x_5);
x_90 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_89);
lean_inc(x_42);
lean_inc(x_15);
x_91 = l_Lean_Syntax_node1(x_15, x_14, x_42);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_40);
lean_ctor_set(x_92, 1, x_89);
x_93 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_25);
lean_inc(x_6);
lean_inc(x_5);
x_94 = l_Lean_Name_mkStr4(x_5, x_6, x_25, x_93);
x_95 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_25);
lean_inc(x_6);
lean_inc(x_5);
x_96 = l_Lean_Name_mkStr4(x_5, x_6, x_25, x_95);
x_97 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_15);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_15);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_5);
x_100 = l_Lean_Name_mkStr4(x_5, x_6, x_25, x_99);
x_101 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_15);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_15);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_mk_string_unchecked("termSatisfies_binder_pred%__", 28, 28);
x_104 = l_Lean_Name_mkStr2(x_5, x_103);
x_105 = lean_mk_string_unchecked("satisfies_binder_pred%", 22, 22);
lean_inc(x_15);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_15);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("pseudo", 6, 6);
x_108 = lean_mk_string_unchecked("antiquot", 8, 8);
lean_inc(x_23);
x_109 = l_Lean_Name_mkStr3(x_23, x_107, x_108);
x_110 = lean_mk_string_unchecked("$", 1, 1);
lean_inc(x_15);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_15);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_mk_string_unchecked("antiquotNestedExpr", 18, 18);
x_113 = l_Lean_Name_mkStr1(x_112);
lean_inc(x_52);
lean_inc(x_15);
x_114 = l_Lean_Syntax_node3(x_15, x_113, x_46, x_29, x_52);
x_115 = lean_mk_string_unchecked("antiquotName", 12, 12);
x_116 = l_Lean_Name_mkStr1(x_115);
lean_inc(x_15);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_15);
lean_ctor_set(x_117, 1, x_23);
lean_inc(x_15);
x_118 = l_Lean_Syntax_node2(x_15, x_116, x_68, x_117);
lean_inc(x_42);
lean_inc(x_15);
x_119 = l_Lean_Syntax_node4(x_15, x_109, x_111, x_42, x_114, x_118);
lean_inc(x_15);
x_120 = l_Lean_Syntax_node3(x_15, x_104, x_106, x_119, x_30);
lean_inc(x_15);
x_121 = l_Lean_Syntax_node3(x_15, x_100, x_102, x_120, x_52);
lean_inc(x_16);
lean_inc(x_15);
x_122 = l_Lean_Syntax_node1(x_15, x_16, x_121);
lean_inc(x_16);
lean_inc(x_15);
x_123 = l_Lean_Syntax_node1(x_15, x_16, x_122);
x_124 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_15);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_15);
lean_ctor_set(x_125, 1, x_124);
lean_inc(x_15);
x_126 = l_Lean_Syntax_node4(x_15, x_96, x_98, x_123, x_125, x_19);
lean_inc(x_16);
lean_inc(x_15);
x_127 = l_Lean_Syntax_node1(x_15, x_16, x_126);
lean_inc(x_15);
x_128 = l_Lean_Syntax_node1(x_15, x_94, x_127);
lean_inc(x_42);
lean_inc(x_15);
x_129 = l_Lean_Syntax_node6(x_15, x_90, x_28, x_42, x_91, x_92, x_42, x_128);
x_130 = l_Lean_Syntax_node2(x_15, x_16, x_88, x_129);
x_131 = l_Lean_Elab_Command_elabCommand(x_130, x_36, x_12, x_11);
return x_131;
}
block_174:
{
lean_object* x_160; lean_object* x_161; 
lean_inc(x_140);
x_160 = l_Array_append(lean_box(0), x_140, x_159);
lean_dec(x_159);
lean_inc(x_139);
lean_inc(x_138);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_138);
lean_ctor_set(x_161, 1, x_139);
lean_ctor_set(x_161, 2, x_160);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_162; 
x_162 = l_Array_empty(lean_box(0));
x_11 = x_133;
x_12 = x_135;
x_13 = x_136;
x_14 = x_137;
x_15 = x_138;
x_16 = x_139;
x_17 = x_140;
x_18 = x_142;
x_19 = x_141;
x_20 = x_143;
x_21 = x_144;
x_22 = x_145;
x_23 = x_146;
x_24 = x_147;
x_25 = x_148;
x_26 = x_149;
x_27 = x_150;
x_28 = x_161;
x_29 = x_151;
x_30 = x_152;
x_31 = x_153;
x_32 = x_154;
x_33 = x_155;
x_34 = x_156;
x_35 = x_157;
x_36 = x_158;
x_37 = x_162;
goto block_132;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_163 = lean_ctor_get(x_134, 0);
lean_inc(x_163);
lean_dec(x_134);
x_164 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_148);
lean_inc(x_6);
lean_inc(x_5);
x_165 = l_Lean_Name_mkStr4(x_5, x_6, x_148, x_164);
x_166 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_138);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_138);
lean_ctor_set(x_167, 1, x_166);
lean_inc(x_140);
x_168 = l_Array_append(lean_box(0), x_140, x_163);
lean_dec(x_163);
lean_inc(x_139);
lean_inc(x_138);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_138);
lean_ctor_set(x_169, 1, x_139);
lean_ctor_set(x_169, 2, x_168);
x_170 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_138);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_138);
lean_ctor_set(x_171, 1, x_170);
lean_inc(x_138);
x_172 = l_Lean_Syntax_node3(x_138, x_165, x_167, x_169, x_171);
x_173 = l_Array_mkArray1___redArg(x_172);
x_11 = x_133;
x_12 = x_135;
x_13 = x_136;
x_14 = x_137;
x_15 = x_138;
x_16 = x_139;
x_17 = x_140;
x_18 = x_142;
x_19 = x_141;
x_20 = x_143;
x_21 = x_144;
x_22 = x_145;
x_23 = x_146;
x_24 = x_147;
x_25 = x_148;
x_26 = x_149;
x_27 = x_150;
x_28 = x_161;
x_29 = x_151;
x_30 = x_152;
x_31 = x_153;
x_32 = x_154;
x_33 = x_155;
x_34 = x_156;
x_35 = x_157;
x_36 = x_158;
x_37 = x_173;
goto block_132;
}
}
block_222:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_193 = l_Lean_Elab_Command_getScope___redArg(x_175, x_189);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Elab_Command_getRef(x_191, x_175, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_Elab_Command_getCurrMacroScope(x_191, x_175, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Lean_Elab_Command_getMainModule___redArg(x_175, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_194, 2);
lean_inc(x_205);
lean_dec(x_194);
x_206 = l_Lean_Name_append(x_205, x_184);
x_207 = lean_box(2);
x_208 = lean_box(0);
x_209 = lean_mk_string_unchecked("binderPred", 10, 10);
lean_inc(x_209);
x_210 = l_Lean_Name_mkStr1(x_209);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_206);
lean_ctor_set(x_211, 2, x_179);
x_212 = lean_unbox(x_208);
x_213 = l_Lean_SourceInfo_fromRef(x_197, x_212);
lean_dec(x_197);
x_214 = lean_mk_string_unchecked("null", 4, 4);
x_215 = l_Lean_Name_mkStr1(x_214);
x_216 = lean_mk_string_unchecked("syntax", 6, 6);
lean_inc(x_216);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_217 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_216);
x_218 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_219; 
x_219 = l_Array_empty(lean_box(0));
x_133 = x_204;
x_134 = x_176;
x_135 = x_175;
x_136 = x_177;
x_137 = x_178;
x_138 = x_213;
x_139 = x_215;
x_140 = x_218;
x_141 = x_182;
x_142 = x_183;
x_143 = x_200;
x_144 = x_203;
x_145 = x_210;
x_146 = x_187;
x_147 = x_207;
x_148 = x_190;
x_149 = x_216;
x_150 = x_180;
x_151 = x_181;
x_152 = x_211;
x_153 = x_209;
x_154 = x_185;
x_155 = x_192;
x_156 = x_217;
x_157 = x_188;
x_158 = x_191;
x_159 = x_219;
goto block_174;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_186, 0);
lean_inc(x_220);
lean_dec(x_186);
x_221 = l_Array_mkArray1___redArg(x_220);
x_133 = x_204;
x_134 = x_176;
x_135 = x_175;
x_136 = x_177;
x_137 = x_178;
x_138 = x_213;
x_139 = x_215;
x_140 = x_218;
x_141 = x_182;
x_142 = x_183;
x_143 = x_200;
x_144 = x_203;
x_145 = x_210;
x_146 = x_187;
x_147 = x_207;
x_148 = x_190;
x_149 = x_216;
x_150 = x_180;
x_151 = x_181;
x_152 = x_211;
x_153 = x_209;
x_154 = x_185;
x_155 = x_192;
x_156 = x_217;
x_157 = x_188;
x_158 = x_191;
x_159 = x_221;
goto block_174;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabBinderPred_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabBinderPred_spec__0(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabBinderPred__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("binderPredicate", 15, 15);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabBinderPred", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabBinderPred), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabBinderPred", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(14u);
x_8 = lean_unsigned_to_nat(40u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(33u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(44u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(58u);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_addBuiltinDeclarationRanges(x_6, x_19, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkBinderPredicate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_23; uint8_t x_24; 
x_8 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_1, x_8);
x_24 = l_Lean_Syntax_isNone(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
x_9 = x_24;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
x_27 = l_Lean_Syntax_getArg(x_26, x_8);
lean_dec(x_26);
x_28 = l_Lean_Syntax_getArg(x_27, x_8);
lean_dec(x_27);
x_29 = l_Lean_Syntax_getKind(x_28);
x_30 = lean_mk_string_unchecked("Lean", 4, 4);
x_31 = lean_mk_string_unchecked("Parser", 6, 6);
x_32 = lean_mk_string_unchecked("Term", 4, 4);
x_33 = lean_mk_string_unchecked("local", 5, 5);
x_34 = l_Lean_Name_mkStr4(x_30, x_31, x_32, x_33);
x_35 = lean_name_eq(x_29, x_34);
lean_dec(x_34);
lean_dec(x_29);
if (x_35 == 0)
{
x_9 = x_24;
goto block_22;
}
else
{
lean_dec(x_2);
goto block_7;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_22:
{
if (x_9 == 0)
{
lean_dec(x_2);
goto block_7;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isNone(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_Syntax_getArg(x_11, x_8);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_13, x_14);
lean_dec(x_13);
x_16 = lean_mk_string_unchecked("binder predicate", 16, 16);
x_17 = l_Lean_Linter_MissingDocs_lintNamed(x_15, x_16, x_2, x_3, x_4);
lean_dec(x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_mk_string_unchecked("binder predicate", 16, 16);
x_21 = l_Lean_Linter_MissingDocs_lint(x_19, x_20, x_2, x_3, x_4);
lean_dec(x_20);
lean_dec(x_19);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkBinderPredicate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkBinderPredicate(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("binderPredicate", 15, 15);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkBinderPredicate___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Linter_MissingDocs_addBuiltinHandler(x_6, x_8, x_1);
return x_9;
}
}
lean_object* initialize_Init_BinderPredicates(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_MissingDocs(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BinderPredicates(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_BinderPredicates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MacroArgUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_MissingDocs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabBinderPred__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabBinderPred_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_checkBinderPredicate__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
