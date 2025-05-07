// Lean compiler output
// Module: Lean.Elab.Macro
// Imports: Lean.Elab.MacroArgUtil
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
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacro_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacro_declRange__1(lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalOptPrio___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacro__1(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacro_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacro_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_SourceInfo_fromRef(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_SourceInfo_fromRef(x_10, x_13);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_54 = lean_mk_string_unchecked("Lean", 4, 4);
x_55 = lean_mk_string_unchecked("Parser", 6, 6);
x_190 = lean_mk_string_unchecked("Command", 7, 7);
x_191 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_192 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_191);
lean_inc(x_1);
x_193 = l_Lean_Syntax_isOfKind(x_1, x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_194 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; size_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; size_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; size_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; size_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_414; lean_object* x_415; lean_object* x_416; size_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_644; uint8_t x_645; 
x_195 = lean_unsigned_to_nat(0u);
x_644 = l_Lean_Syntax_getArg(x_1, x_195);
x_645 = l_Lean_Syntax_isNone(x_644);
if (x_645 == 0)
{
lean_object* x_646; uint8_t x_647; 
x_646 = lean_unsigned_to_nat(1u);
lean_inc(x_644);
x_647 = l_Lean_Syntax_matchesNull(x_644, x_646);
if (x_647 == 0)
{
lean_object* x_648; 
lean_dec(x_644);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_648 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
return x_648;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; 
x_649 = l_Lean_Syntax_getArg(x_644, x_195);
lean_dec(x_644);
x_650 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_651 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_650);
lean_inc(x_649);
x_652 = l_Lean_Syntax_isOfKind(x_649, x_651);
lean_dec(x_651);
if (x_652 == 0)
{
lean_object* x_653; 
lean_dec(x_649);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_653 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
return x_653;
}
else
{
lean_object* x_654; 
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_649);
x_624 = x_654;
x_625 = x_2;
x_626 = x_3;
x_627 = x_4;
goto block_643;
}
}
}
else
{
lean_object* x_655; 
lean_dec(x_644);
x_655 = lean_box(0);
x_624 = x_655;
x_625 = x_2;
x_626 = x_3;
x_627 = x_4;
goto block_643;
}
block_289:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; size_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_227 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_227);
lean_inc(x_221);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_227);
lean_inc(x_228);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_221);
x_229 = l_Lean_Syntax_node5(x_221, x_213, x_198, x_204, x_199, x_226, x_228);
lean_inc(x_212);
lean_inc(x_221);
x_230 = l_Lean_Syntax_node1(x_221, x_212, x_229);
x_231 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_232 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_231);
x_233 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_221);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_221);
lean_ctor_set(x_234, 1, x_233);
x_235 = l___private_Init_Data_Repr_0__Nat_reprFast(x_196);
lean_inc(x_215);
x_236 = l_Lean_Syntax_mkNumLit(x_235, x_215);
lean_inc(x_221);
x_237 = l_Lean_Syntax_node5(x_221, x_232, x_198, x_234, x_199, x_236, x_228);
lean_inc(x_212);
lean_inc(x_221);
x_238 = l_Lean_Syntax_node1(x_221, x_212, x_237);
x_239 = lean_array_size(x_224);
x_240 = l_Array_mapMUnsafe_map___at___Lean_Parser_Tactic___aux__Init__Meta______macroRules__Lean__Parser__Tactic__tacticErw________1_spec__0(x_239, x_211, x_224);
lean_inc(x_219);
x_241 = l_Array_append(lean_box(0), x_219, x_240);
lean_dec(x_240);
lean_inc(x_212);
lean_inc(x_221);
x_242 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_242, 0, x_221);
lean_ctor_set(x_242, 1, x_212);
lean_ctor_set(x_242, 2, x_241);
x_243 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_221);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_221);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_unsigned_to_nat(10u);
x_246 = lean_mk_empty_array_with_capacity(x_245);
x_247 = lean_array_push(x_246, x_197);
x_248 = lean_array_push(x_247, x_206);
x_249 = lean_array_push(x_248, x_225);
x_250 = lean_array_push(x_249, x_210);
x_251 = lean_array_push(x_250, x_222);
x_252 = lean_array_push(x_251, x_230);
x_253 = lean_array_push(x_252, x_238);
x_254 = lean_array_push(x_253, x_242);
x_255 = lean_array_push(x_254, x_244);
x_256 = lean_array_push(x_255, x_207);
x_257 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_257, 0, x_221);
lean_ctor_set(x_257, 1, x_205);
lean_ctor_set(x_257, 2, x_256);
x_258 = l_Lean_Syntax_getArgs(x_214);
x_259 = lean_array_get_size(x_258);
lean_dec(x_258);
x_260 = lean_nat_dec_eq(x_259, x_217);
lean_dec(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_202);
lean_dec(x_201);
x_261 = l_Lean_Elab_Command_elabMacro___lam__0(x_223, x_208, x_220);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l_Lean_Elab_Command_getCurrMacroScope(x_223, x_208, x_263);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l_Lean_Elab_Command_getMainModule___redArg(x_208, x_265);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_Lean_Syntax_getArg(x_214, x_217);
lean_dec(x_214);
x_269 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_269);
lean_inc(x_55);
lean_inc(x_54);
x_270 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_269);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_271; 
x_271 = l_Array_empty(lean_box(0));
x_56 = x_209;
x_57 = x_208;
x_58 = x_268;
x_59 = x_212;
x_60 = x_215;
x_61 = x_200;
x_62 = x_262;
x_63 = x_216;
x_64 = x_227;
x_65 = x_267;
x_66 = x_257;
x_67 = x_219;
x_68 = x_218;
x_69 = x_270;
x_70 = x_223;
x_71 = x_269;
x_72 = x_271;
goto block_99;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_203, 0);
lean_inc(x_272);
lean_dec(x_203);
x_273 = l_Array_mkArray1___redArg(x_272);
x_56 = x_209;
x_57 = x_208;
x_58 = x_268;
x_59 = x_212;
x_60 = x_215;
x_61 = x_200;
x_62 = x_262;
x_63 = x_216;
x_64 = x_227;
x_65 = x_267;
x_66 = x_257;
x_67 = x_219;
x_68 = x_218;
x_69 = x_270;
x_70 = x_223;
x_71 = x_269;
x_72 = x_273;
goto block_99;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_274 = l_Lean_Elab_Command_elabMacro___lam__0(x_223, x_208, x_220);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = l_Lean_Elab_Command_getCurrMacroScope(x_223, x_208, x_276);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Lean_Elab_Command_getMainModule___redArg(x_208, x_279);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_Syntax_getArg(x_214, x_195);
lean_dec(x_214);
x_284 = lean_mk_string_unchecked("macro_rules", 11, 11);
lean_inc(x_284);
lean_inc(x_55);
lean_inc(x_54);
x_285 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_284);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_286; 
x_286 = l_Array_empty(lean_box(0));
x_100 = x_285;
x_101 = x_282;
x_102 = x_208;
x_103 = x_209;
x_104 = x_281;
x_105 = x_275;
x_106 = x_212;
x_107 = x_278;
x_108 = x_215;
x_109 = x_200;
x_110 = x_217;
x_111 = x_283;
x_112 = x_216;
x_113 = x_227;
x_114 = x_257;
x_115 = x_219;
x_116 = x_218;
x_117 = x_202;
x_118 = x_201;
x_119 = x_223;
x_120 = x_284;
x_121 = x_286;
goto block_189;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_203, 0);
lean_inc(x_287);
lean_dec(x_203);
x_288 = l_Array_mkArray1___redArg(x_287);
x_100 = x_285;
x_101 = x_282;
x_102 = x_208;
x_103 = x_209;
x_104 = x_281;
x_105 = x_275;
x_106 = x_212;
x_107 = x_278;
x_108 = x_215;
x_109 = x_200;
x_110 = x_217;
x_111 = x_283;
x_112 = x_216;
x_113 = x_227;
x_114 = x_257;
x_115 = x_219;
x_116 = x_218;
x_117 = x_202;
x_118 = x_201;
x_119 = x_223;
x_120 = x_284;
x_121 = x_288;
goto block_189;
}
}
}
block_330:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_inc(x_309);
x_318 = l_Array_append(lean_box(0), x_309, x_317);
lean_dec(x_317);
lean_inc(x_303);
lean_inc(x_312);
x_319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_319, 0, x_312);
lean_ctor_set(x_319, 1, x_303);
lean_ctor_set(x_319, 2, x_318);
x_320 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_321 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_320);
x_322 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_322);
lean_inc(x_312);
x_323 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_323, 0, x_312);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_312);
x_325 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_325, 0, x_312);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_312);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_312);
lean_ctor_set(x_327, 1, x_326);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_328; 
x_328 = l_Lean_mkIdentFrom(x_316, x_292, x_193);
lean_dec(x_316);
x_196 = x_290;
x_197 = x_291;
x_198 = x_323;
x_199 = x_327;
x_200 = x_293;
x_201 = x_322;
x_202 = x_294;
x_203 = x_295;
x_204 = x_325;
x_205 = x_297;
x_206 = x_298;
x_207 = x_299;
x_208 = x_301;
x_209 = x_300;
x_210 = x_302;
x_211 = x_304;
x_212 = x_303;
x_213 = x_321;
x_214 = x_305;
x_215 = x_306;
x_216 = x_307;
x_217 = x_308;
x_218 = x_310;
x_219 = x_309;
x_220 = x_311;
x_221 = x_312;
x_222 = x_319;
x_223 = x_313;
x_224 = x_314;
x_225 = x_315;
x_226 = x_328;
goto block_289;
}
else
{
lean_object* x_329; 
lean_dec(x_316);
lean_dec(x_292);
x_329 = lean_ctor_get(x_296, 0);
lean_inc(x_329);
lean_dec(x_296);
x_196 = x_290;
x_197 = x_291;
x_198 = x_323;
x_199 = x_327;
x_200 = x_293;
x_201 = x_322;
x_202 = x_294;
x_203 = x_295;
x_204 = x_325;
x_205 = x_297;
x_206 = x_298;
x_207 = x_299;
x_208 = x_301;
x_209 = x_300;
x_210 = x_302;
x_211 = x_304;
x_212 = x_303;
x_213 = x_321;
x_214 = x_305;
x_215 = x_306;
x_216 = x_307;
x_217 = x_308;
x_218 = x_310;
x_219 = x_309;
x_220 = x_311;
x_221 = x_312;
x_222 = x_319;
x_223 = x_313;
x_224 = x_314;
x_225 = x_315;
x_226 = x_329;
goto block_289;
}
}
block_370:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_inc(x_349);
x_359 = l_Array_append(lean_box(0), x_349, x_358);
lean_dec(x_358);
lean_inc(x_343);
lean_inc(x_352);
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_352);
lean_ctor_set(x_360, 1, x_343);
lean_ctor_set(x_360, 2, x_359);
lean_inc(x_352);
x_361 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_361, 0, x_352);
lean_ctor_set(x_361, 1, x_342);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_362; 
x_362 = l_Array_empty(lean_box(0));
x_290 = x_331;
x_291 = x_332;
x_292 = x_333;
x_293 = x_334;
x_294 = x_335;
x_295 = x_336;
x_296 = x_337;
x_297 = x_338;
x_298 = x_360;
x_299 = x_339;
x_300 = x_340;
x_301 = x_341;
x_302 = x_361;
x_303 = x_343;
x_304 = x_344;
x_305 = x_345;
x_306 = x_346;
x_307 = x_347;
x_308 = x_348;
x_309 = x_349;
x_310 = x_350;
x_311 = x_351;
x_312 = x_352;
x_313 = x_353;
x_314 = x_354;
x_315 = x_355;
x_316 = x_356;
x_317 = x_362;
goto block_330;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_363 = lean_ctor_get(x_357, 0);
lean_inc(x_363);
lean_dec(x_357);
x_364 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_55);
lean_inc(x_54);
x_365 = l_Lean_Name_mkStr3(x_54, x_55, x_364);
x_366 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_352);
x_367 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_367, 0, x_352);
lean_ctor_set(x_367, 1, x_366);
lean_inc(x_352);
x_368 = l_Lean_Syntax_node2(x_352, x_365, x_367, x_363);
x_369 = l_Array_mkArray1___redArg(x_368);
x_290 = x_331;
x_291 = x_332;
x_292 = x_333;
x_293 = x_334;
x_294 = x_335;
x_295 = x_336;
x_296 = x_337;
x_297 = x_338;
x_298 = x_360;
x_299 = x_339;
x_300 = x_340;
x_301 = x_341;
x_302 = x_361;
x_303 = x_343;
x_304 = x_344;
x_305 = x_345;
x_306 = x_346;
x_307 = x_347;
x_308 = x_348;
x_309 = x_349;
x_310 = x_350;
x_311 = x_351;
x_312 = x_352;
x_313 = x_353;
x_314 = x_354;
x_315 = x_355;
x_316 = x_356;
x_317 = x_369;
goto block_330;
}
}
block_413:
{
lean_object* x_399; lean_object* x_400; 
lean_inc(x_389);
x_399 = l_Array_append(lean_box(0), x_389, x_398);
lean_dec(x_398);
lean_inc(x_382);
lean_inc(x_392);
x_400 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_400, 0, x_392);
lean_ctor_set(x_400, 1, x_382);
lean_ctor_set(x_400, 2, x_399);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_401; 
x_401 = l_Array_empty(lean_box(0));
x_331 = x_371;
x_332 = x_400;
x_333 = x_372;
x_334 = x_373;
x_335 = x_374;
x_336 = x_375;
x_337 = x_376;
x_338 = x_377;
x_339 = x_378;
x_340 = x_380;
x_341 = x_379;
x_342 = x_381;
x_343 = x_382;
x_344 = x_383;
x_345 = x_384;
x_346 = x_385;
x_347 = x_387;
x_348 = x_388;
x_349 = x_389;
x_350 = x_390;
x_351 = x_391;
x_352 = x_392;
x_353 = x_393;
x_354 = x_394;
x_355 = x_395;
x_356 = x_396;
x_357 = x_397;
x_358 = x_401;
goto block_370;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_402 = lean_ctor_get(x_386, 0);
lean_inc(x_402);
lean_dec(x_386);
x_403 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_390);
lean_inc(x_55);
lean_inc(x_54);
x_404 = l_Lean_Name_mkStr4(x_54, x_55, x_390, x_403);
x_405 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_392);
x_406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_406, 0, x_392);
lean_ctor_set(x_406, 1, x_405);
lean_inc(x_389);
x_407 = l_Array_append(lean_box(0), x_389, x_402);
lean_dec(x_402);
lean_inc(x_382);
lean_inc(x_392);
x_408 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_408, 0, x_392);
lean_ctor_set(x_408, 1, x_382);
lean_ctor_set(x_408, 2, x_407);
x_409 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_392);
x_410 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_410, 0, x_392);
lean_ctor_set(x_410, 1, x_409);
lean_inc(x_392);
x_411 = l_Lean_Syntax_node3(x_392, x_404, x_406, x_408, x_410);
x_412 = l_Array_mkArray1___redArg(x_411);
x_331 = x_371;
x_332 = x_400;
x_333 = x_372;
x_334 = x_373;
x_335 = x_374;
x_336 = x_375;
x_337 = x_376;
x_338 = x_377;
x_339 = x_378;
x_340 = x_380;
x_341 = x_379;
x_342 = x_381;
x_343 = x_382;
x_344 = x_383;
x_345 = x_384;
x_346 = x_385;
x_347 = x_387;
x_348 = x_388;
x_349 = x_389;
x_350 = x_390;
x_351 = x_391;
x_352 = x_392;
x_353 = x_393;
x_354 = x_394;
x_355 = x_395;
x_356 = x_396;
x_357 = x_397;
x_358 = x_412;
goto block_370;
}
}
block_459:
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_437 = l_Lean_Elab_Command_getScope___redArg(x_435, x_436);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_440 = l_Lean_Elab_Command_getRef(x_434, x_435, x_439);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = l_Lean_Elab_Command_getCurrMacroScope(x_434, x_435, x_442);
x_444 = lean_ctor_get(x_443, 1);
lean_inc(x_444);
lean_dec(x_443);
x_445 = l_Lean_Elab_Command_getMainModule___redArg(x_435, x_444);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
x_447 = lean_ctor_get(x_438, 2);
lean_inc(x_447);
lean_dec(x_438);
lean_inc(x_433);
x_448 = l_Lean_Name_append(x_447, x_433);
x_449 = lean_box(0);
lean_inc(x_419);
x_450 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_450, 0, x_419);
lean_ctor_set(x_450, 1, x_448);
lean_ctor_set(x_450, 2, x_424);
x_451 = lean_unbox(x_449);
x_452 = l_Lean_SourceInfo_fromRef(x_441, x_451);
lean_dec(x_441);
x_453 = lean_mk_string_unchecked("syntax", 6, 6);
lean_inc(x_453);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_454 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_453);
x_455 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_456; 
x_456 = l_Array_empty(lean_box(0));
x_371 = x_414;
x_372 = x_433;
x_373 = x_421;
x_374 = x_426;
x_375 = x_427;
x_376 = x_430;
x_377 = x_454;
x_378 = x_415;
x_379 = x_435;
x_380 = x_450;
x_381 = x_453;
x_382 = x_416;
x_383 = x_417;
x_384 = x_418;
x_385 = x_419;
x_386 = x_420;
x_387 = x_423;
x_388 = x_422;
x_389 = x_455;
x_390 = x_425;
x_391 = x_446;
x_392 = x_452;
x_393 = x_434;
x_394 = x_429;
x_395 = x_428;
x_396 = x_431;
x_397 = x_432;
x_398 = x_456;
goto block_413;
}
else
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_427, 0);
lean_inc(x_457);
x_458 = l_Array_mkArray1___redArg(x_457);
x_371 = x_414;
x_372 = x_433;
x_373 = x_421;
x_374 = x_426;
x_375 = x_427;
x_376 = x_430;
x_377 = x_454;
x_378 = x_415;
x_379 = x_435;
x_380 = x_450;
x_381 = x_453;
x_382 = x_416;
x_383 = x_417;
x_384 = x_418;
x_385 = x_419;
x_386 = x_420;
x_387 = x_423;
x_388 = x_422;
x_389 = x_455;
x_390 = x_425;
x_391 = x_446;
x_392 = x_452;
x_393 = x_434;
x_394 = x_429;
x_395 = x_428;
x_396 = x_431;
x_397 = x_432;
x_398 = x_458;
goto block_413;
}
}
block_542:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_474 = lean_unsigned_to_nat(8u);
x_475 = l_Lean_Syntax_getArg(x_1, x_474);
x_476 = lean_mk_string_unchecked("macroTail", 9, 9);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_477 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_476);
lean_inc(x_475);
x_478 = l_Lean_Syntax_isOfKind(x_475, x_477);
lean_dec(x_477);
if (x_478 == 0)
{
lean_object* x_479; 
lean_dec(x_475);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_479 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_471, x_472, x_473);
lean_dec(x_472);
return x_479;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; lean_object* x_505; 
x_480 = lean_unsigned_to_nat(7u);
x_481 = l_Lean_Elab_Command_getRef(x_471, x_472, x_473);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = l_Lean_Syntax_getArg(x_1, x_464);
x_485 = lean_mk_empty_array_with_capacity(x_465);
lean_inc(x_484);
lean_inc(x_485);
x_486 = lean_array_push(x_485, x_484);
x_487 = lean_mk_string_unchecked("null", 4, 4);
x_488 = l_Lean_Syntax_getArg(x_475, x_464);
lean_inc(x_488);
x_489 = lean_array_push(x_486, x_488);
x_490 = l_Lean_Name_mkStr1(x_487);
x_491 = lean_box(2);
lean_inc(x_490);
x_492 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_490);
lean_ctor_set(x_492, 2, x_489);
x_493 = lean_alloc_closure((void*)(l_Lean_evalOptPrio___boxed), 3, 1);
lean_closure_set(x_493, 0, x_470);
x_494 = l_Lean_replaceRef(x_492, x_482);
lean_dec(x_482);
lean_dec(x_492);
x_495 = lean_ctor_get(x_471, 0);
x_496 = lean_ctor_get(x_471, 1);
x_497 = lean_ctor_get(x_471, 2);
x_498 = lean_ctor_get(x_471, 3);
x_499 = lean_ctor_get(x_471, 4);
x_500 = lean_ctor_get(x_471, 5);
x_501 = lean_ctor_get(x_471, 7);
x_502 = lean_ctor_get(x_471, 8);
x_503 = lean_ctor_get_uint8(x_471, sizeof(void*)*9);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_inc(x_497);
lean_inc(x_496);
lean_inc(x_495);
x_504 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_504, 0, x_495);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_498);
lean_ctor_set(x_504, 4, x_499);
lean_ctor_set(x_504, 5, x_500);
lean_ctor_set(x_504, 6, x_494);
lean_ctor_set(x_504, 7, x_501);
lean_ctor_set(x_504, 8, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*9, x_503);
x_505 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_493, x_504, x_472, x_483);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; size_t x_510; size_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = l_Lean_Syntax_getArg(x_1, x_480);
lean_dec(x_1);
x_509 = l_Lean_Syntax_getArgs(x_508);
lean_dec(x_508);
x_510 = lean_array_size(x_509);
x_511 = lean_usize_of_nat(x_195);
lean_inc(x_504);
x_512 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacro_spec__0(x_510, x_511, x_509, x_504, x_472, x_507);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = l_Array_unzip___redArg(x_513);
lean_dec(x_513);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = l_Lean_Syntax_getArg(x_475, x_461);
lean_dec(x_475);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_519 = l_Lean_Syntax_getId(x_518);
lean_inc(x_516);
lean_inc(x_490);
x_520 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_520, 0, x_491);
lean_ctor_set(x_520, 1, x_490);
lean_ctor_set(x_520, 2, x_516);
x_521 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkNameFromParserSyntax___boxed), 4, 2);
lean_closure_set(x_521, 0, x_519);
lean_closure_set(x_521, 1, x_520);
x_522 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_521, x_504, x_472, x_514);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
lean_inc(x_466);
x_525 = l_Lean_Elab_Command_addMacroScopeIfLocal___at___Lean_Elab_Command_elabSyntax_spec__1(x_523, x_466, x_504, x_472, x_524);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
lean_inc(x_518);
x_414 = x_506;
x_415 = x_518;
x_416 = x_490;
x_417 = x_511;
x_418 = x_488;
x_419 = x_491;
x_420 = x_468;
x_421 = x_485;
x_422 = x_461;
x_423 = x_460;
x_424 = x_517;
x_425 = x_462;
x_426 = x_518;
x_427 = x_463;
x_428 = x_466;
x_429 = x_516;
x_430 = x_467;
x_431 = x_484;
x_432 = x_469;
x_433 = x_526;
x_434 = x_504;
x_435 = x_472;
x_436 = x_527;
goto block_459;
}
else
{
uint8_t x_528; 
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_490);
lean_dec(x_488);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_472);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
x_528 = !lean_is_exclusive(x_522);
if (x_528 == 0)
{
return x_522;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_522, 0);
x_530 = lean_ctor_get(x_522, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_522);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
else
{
lean_object* x_532; lean_object* x_533; 
x_532 = lean_ctor_get(x_467, 0);
lean_inc(x_532);
x_533 = l_Lean_Syntax_getId(x_532);
lean_dec(x_532);
lean_inc(x_518);
x_414 = x_506;
x_415 = x_518;
x_416 = x_490;
x_417 = x_511;
x_418 = x_488;
x_419 = x_491;
x_420 = x_468;
x_421 = x_485;
x_422 = x_461;
x_423 = x_460;
x_424 = x_517;
x_425 = x_462;
x_426 = x_518;
x_427 = x_463;
x_428 = x_466;
x_429 = x_516;
x_430 = x_467;
x_431 = x_484;
x_432 = x_469;
x_433 = x_533;
x_434 = x_504;
x_435 = x_472;
x_436 = x_514;
goto block_459;
}
}
else
{
uint8_t x_534; 
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_490);
lean_dec(x_488);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_475);
lean_dec(x_472);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
x_534 = !lean_is_exclusive(x_512);
if (x_534 == 0)
{
return x_512;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_512, 0);
x_536 = lean_ctor_get(x_512, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_512);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
else
{
uint8_t x_538; 
lean_dec(x_504);
lean_dec(x_490);
lean_dec(x_488);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_475);
lean_dec(x_472);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_538 = !lean_is_exclusive(x_505);
if (x_538 == 0)
{
return x_505;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_505, 0);
x_540 = lean_ctor_get(x_505, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_505);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
}
}
block_569:
{
lean_object* x_556; lean_object* x_557; uint8_t x_558; 
x_556 = lean_unsigned_to_nat(6u);
x_557 = l_Lean_Syntax_getArg(x_1, x_556);
x_558 = l_Lean_Syntax_isNone(x_557);
if (x_558 == 0)
{
uint8_t x_559; 
lean_inc(x_557);
x_559 = l_Lean_Syntax_matchesNull(x_557, x_543);
if (x_559 == 0)
{
lean_object* x_560; 
lean_dec(x_557);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_560 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_553, x_554, x_555);
lean_dec(x_554);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_564; 
x_561 = l_Lean_Syntax_getArg(x_557, x_195);
lean_dec(x_557);
x_562 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_563 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_562);
lean_inc(x_561);
x_564 = l_Lean_Syntax_isOfKind(x_561, x_563);
lean_dec(x_563);
if (x_564 == 0)
{
lean_object* x_565; 
lean_dec(x_561);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_565 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_553, x_554, x_555);
lean_dec(x_554);
return x_565;
}
else
{
lean_object* x_566; lean_object* x_567; 
x_566 = l_Lean_Syntax_getArg(x_561, x_547);
lean_dec(x_561);
x_567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_567, 0, x_566);
x_460 = x_544;
x_461 = x_543;
x_462 = x_545;
x_463 = x_546;
x_464 = x_547;
x_465 = x_548;
x_466 = x_549;
x_467 = x_552;
x_468 = x_550;
x_469 = x_551;
x_470 = x_567;
x_471 = x_553;
x_472 = x_554;
x_473 = x_555;
goto block_542;
}
}
}
else
{
lean_object* x_568; 
lean_dec(x_557);
x_568 = lean_box(0);
x_460 = x_544;
x_461 = x_543;
x_462 = x_545;
x_463 = x_546;
x_464 = x_547;
x_465 = x_548;
x_466 = x_549;
x_467 = x_552;
x_468 = x_550;
x_469 = x_551;
x_470 = x_568;
x_471 = x_553;
x_472 = x_554;
x_473 = x_555;
goto block_542;
}
}
block_595:
{
lean_object* x_582; lean_object* x_583; uint8_t x_584; 
x_582 = lean_unsigned_to_nat(5u);
x_583 = l_Lean_Syntax_getArg(x_1, x_582);
x_584 = l_Lean_Syntax_isNone(x_583);
if (x_584 == 0)
{
uint8_t x_585; 
lean_inc(x_583);
x_585 = l_Lean_Syntax_matchesNull(x_583, x_571);
if (x_585 == 0)
{
lean_object* x_586; 
lean_dec(x_583);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_586 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_579, x_580, x_581);
lean_dec(x_580);
return x_586;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; 
x_587 = l_Lean_Syntax_getArg(x_583, x_195);
lean_dec(x_583);
x_588 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_190);
lean_inc(x_55);
lean_inc(x_54);
x_589 = l_Lean_Name_mkStr4(x_54, x_55, x_190, x_588);
lean_inc(x_587);
x_590 = l_Lean_Syntax_isOfKind(x_587, x_589);
lean_dec(x_589);
if (x_590 == 0)
{
lean_object* x_591; 
lean_dec(x_587);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_591 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_579, x_580, x_581);
lean_dec(x_580);
return x_591;
}
else
{
lean_object* x_592; lean_object* x_593; 
x_592 = l_Lean_Syntax_getArg(x_587, x_574);
lean_dec(x_587);
x_593 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_593, 0, x_592);
x_543 = x_571;
x_544 = x_570;
x_545 = x_572;
x_546 = x_573;
x_547 = x_574;
x_548 = x_575;
x_549 = x_576;
x_550 = x_577;
x_551 = x_578;
x_552 = x_593;
x_553 = x_579;
x_554 = x_580;
x_555 = x_581;
goto block_569;
}
}
}
else
{
lean_object* x_594; 
lean_dec(x_583);
x_594 = lean_box(0);
x_543 = x_571;
x_544 = x_570;
x_545 = x_572;
x_546 = x_573;
x_547 = x_574;
x_548 = x_575;
x_549 = x_576;
x_550 = x_577;
x_551 = x_578;
x_552 = x_594;
x_553 = x_579;
x_554 = x_580;
x_555 = x_581;
goto block_569;
}
}
block_623:
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_602 = lean_unsigned_to_nat(2u);
x_603 = l_Lean_Syntax_getArg(x_1, x_602);
x_604 = lean_mk_string_unchecked("Term", 4, 4);
x_605 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_604);
lean_inc(x_55);
lean_inc(x_54);
x_606 = l_Lean_Name_mkStr4(x_54, x_55, x_604, x_605);
lean_inc(x_603);
x_607 = l_Lean_Syntax_isOfKind(x_603, x_606);
if (x_607 == 0)
{
lean_object* x_608; 
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_608 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_599, x_600, x_601);
lean_dec(x_600);
return x_608;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; 
x_609 = lean_unsigned_to_nat(3u);
x_610 = lean_unsigned_to_nat(4u);
x_611 = l_Lean_Syntax_getArg(x_1, x_610);
x_612 = l_Lean_Syntax_isNone(x_611);
if (x_612 == 0)
{
uint8_t x_613; 
lean_inc(x_611);
x_613 = l_Lean_Syntax_matchesNull(x_611, x_596);
if (x_613 == 0)
{
lean_object* x_614; 
lean_dec(x_611);
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_614 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_599, x_600, x_601);
lean_dec(x_600);
return x_614;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; 
x_615 = l_Lean_Syntax_getArg(x_611, x_195);
lean_dec(x_611);
x_616 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_55);
lean_inc(x_54);
x_617 = l_Lean_Name_mkStr3(x_54, x_55, x_616);
lean_inc(x_615);
x_618 = l_Lean_Syntax_isOfKind(x_615, x_617);
lean_dec(x_617);
if (x_618 == 0)
{
lean_object* x_619; 
lean_dec(x_615);
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_619 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_599, x_600, x_601);
lean_dec(x_600);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; 
x_620 = l_Lean_Syntax_getArg(x_615, x_596);
lean_dec(x_615);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_620);
x_570 = x_606;
x_571 = x_596;
x_572 = x_604;
x_573 = x_597;
x_574 = x_609;
x_575 = x_602;
x_576 = x_603;
x_577 = x_598;
x_578 = x_621;
x_579 = x_599;
x_580 = x_600;
x_581 = x_601;
goto block_595;
}
}
}
else
{
lean_object* x_622; 
lean_dec(x_611);
x_622 = lean_box(0);
x_570 = x_606;
x_571 = x_596;
x_572 = x_604;
x_573 = x_597;
x_574 = x_609;
x_575 = x_602;
x_576 = x_603;
x_577 = x_598;
x_578 = x_622;
x_579 = x_599;
x_580 = x_600;
x_581 = x_601;
goto block_595;
}
}
}
block_643:
{
lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_628 = lean_unsigned_to_nat(1u);
x_629 = l_Lean_Syntax_getArg(x_1, x_628);
x_630 = l_Lean_Syntax_isNone(x_629);
if (x_630 == 0)
{
uint8_t x_631; 
lean_inc(x_629);
x_631 = l_Lean_Syntax_matchesNull(x_629, x_628);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_629);
lean_dec(x_624);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_632 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_625, x_626, x_627);
lean_dec(x_626);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; 
x_633 = l_Lean_Syntax_getArg(x_629, x_195);
lean_dec(x_629);
x_634 = lean_mk_string_unchecked("Term", 4, 4);
x_635 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_55);
lean_inc(x_54);
x_636 = l_Lean_Name_mkStr4(x_54, x_55, x_634, x_635);
lean_inc(x_633);
x_637 = l_Lean_Syntax_isOfKind(x_633, x_636);
lean_dec(x_636);
if (x_637 == 0)
{
lean_object* x_638; 
lean_dec(x_633);
lean_dec(x_624);
lean_dec(x_190);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_1);
x_638 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_625, x_626, x_627);
lean_dec(x_626);
return x_638;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = l_Lean_Syntax_getArg(x_633, x_628);
lean_dec(x_633);
x_640 = l_Lean_Syntax_getArgs(x_639);
lean_dec(x_639);
x_641 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_641, 0, x_640);
x_596 = x_628;
x_597 = x_624;
x_598 = x_641;
x_599 = x_625;
x_600 = x_626;
x_601 = x_627;
goto block_623;
}
}
}
else
{
lean_object* x_642; 
lean_dec(x_629);
x_642 = lean_box(0);
x_596 = x_628;
x_597 = x_624;
x_598 = x_642;
x_599 = x_625;
x_600 = x_626;
x_601 = x_627;
goto block_623;
}
}
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_push(x_8, x_5);
x_14 = lean_array_push(x_13, x_9);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lean_Elab_Command_elabCommand(x_15, x_10, x_11, x_12);
return x_16;
}
block_53:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_29);
lean_inc(x_20);
x_44 = l_Lean_Syntax_node1(x_20, x_29, x_43);
lean_inc(x_33);
lean_inc(x_20);
x_45 = l_Lean_Syntax_node2(x_20, x_33, x_37, x_44);
lean_inc(x_20);
x_46 = l_Lean_Syntax_node3(x_20, x_42, x_36, x_45, x_24);
lean_inc(x_29);
lean_inc(x_20);
x_47 = l_Lean_Syntax_node2(x_20, x_29, x_46, x_35);
lean_inc(x_20);
x_48 = l_Lean_Syntax_node2(x_20, x_33, x_23, x_47);
lean_inc(x_20);
x_49 = l_Lean_Syntax_node4(x_20, x_31, x_41, x_34, x_25, x_48);
lean_inc(x_29);
lean_inc(x_20);
x_50 = l_Lean_Syntax_node1(x_20, x_29, x_49);
lean_inc(x_20);
x_51 = l_Lean_Syntax_node1(x_20, x_39, x_50);
lean_inc(x_18);
x_52 = l_Lean_Syntax_node6(x_20, x_27, x_26, x_18, x_38, x_30, x_18, x_51);
x_5 = x_22;
x_6 = x_29;
x_7 = x_32;
x_8 = x_21;
x_9 = x_52;
x_10 = x_40;
x_11 = x_28;
x_12 = x_19;
goto block_17;
}
block_99:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_inc(x_67);
x_73 = l_Array_append(lean_box(0), x_67, x_72);
lean_dec(x_72);
lean_inc(x_59);
lean_inc(x_62);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_59);
lean_ctor_set(x_74, 2, x_73);
lean_inc(x_59);
lean_inc(x_62);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_62);
lean_ctor_set(x_75, 1, x_59);
lean_ctor_set(x_75, 2, x_67);
lean_inc(x_75);
lean_inc(x_62);
x_76 = l_Lean_Syntax_node1(x_62, x_63, x_75);
lean_inc(x_62);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_71);
x_78 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_68);
lean_inc(x_55);
lean_inc(x_54);
x_79 = l_Lean_Name_mkStr4(x_54, x_55, x_68, x_78);
x_80 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_68);
lean_inc(x_55);
lean_inc(x_54);
x_81 = l_Lean_Name_mkStr4(x_54, x_55, x_68, x_80);
x_82 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_62);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("quot", 4, 4);
x_85 = l_Lean_Name_mkStr4(x_54, x_55, x_68, x_84);
x_86 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_62);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_62);
lean_ctor_set(x_87, 1, x_86);
lean_inc(x_62);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_62);
lean_ctor_set(x_88, 1, x_64);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_85);
lean_inc(x_62);
x_89 = l_Lean_Syntax_node3(x_62, x_85, x_87, x_56, x_88);
lean_inc(x_59);
lean_inc(x_62);
x_90 = l_Lean_Syntax_node1(x_62, x_59, x_89);
lean_inc(x_59);
lean_inc(x_62);
x_91 = l_Lean_Syntax_node1(x_62, x_59, x_90);
x_92 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_62);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_62);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_62);
x_94 = l_Lean_Syntax_node3(x_62, x_85, x_87, x_58, x_88);
lean_inc(x_62);
x_95 = l_Lean_Syntax_node4(x_62, x_81, x_83, x_91, x_93, x_94);
lean_inc(x_59);
lean_inc(x_62);
x_96 = l_Lean_Syntax_node1(x_62, x_59, x_95);
lean_inc(x_62);
x_97 = l_Lean_Syntax_node1(x_62, x_79, x_96);
lean_inc(x_75);
x_98 = l_Lean_Syntax_node6(x_62, x_69, x_74, x_75, x_76, x_77, x_75, x_97);
x_5 = x_66;
x_6 = x_59;
x_7 = x_60;
x_8 = x_61;
x_9 = x_98;
x_10 = x_70;
x_11 = x_57;
x_12 = x_65;
goto block_17;
}
block_189:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_inc(x_115);
x_122 = l_Array_append(lean_box(0), x_115, x_121);
lean_dec(x_121);
lean_inc(x_106);
lean_inc(x_105);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_105);
lean_ctor_set(x_123, 1, x_106);
lean_ctor_set(x_123, 2, x_122);
lean_inc(x_106);
lean_inc(x_105);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_105);
lean_ctor_set(x_124, 1, x_106);
lean_ctor_set(x_124, 2, x_115);
lean_inc(x_124);
lean_inc(x_105);
x_125 = l_Lean_Syntax_node1(x_105, x_112, x_124);
lean_inc(x_105);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_105);
lean_ctor_set(x_126, 1, x_120);
x_127 = lean_mk_string_unchecked("matchAlts", 9, 9);
lean_inc(x_116);
lean_inc(x_55);
lean_inc(x_54);
x_128 = l_Lean_Name_mkStr4(x_54, x_55, x_116, x_127);
x_129 = lean_mk_string_unchecked("matchAlt", 8, 8);
lean_inc(x_116);
lean_inc(x_55);
lean_inc(x_54);
x_130 = l_Lean_Name_mkStr4(x_54, x_55, x_116, x_129);
x_131 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_105);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_105);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_116);
lean_inc(x_55);
lean_inc(x_54);
x_134 = l_Lean_Name_mkStr4(x_54, x_55, x_116, x_133);
x_135 = lean_mk_string_unchecked("`(", 2, 2);
lean_inc(x_105);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_105);
lean_ctor_set(x_136, 1, x_135);
lean_inc(x_105);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_105);
lean_ctor_set(x_137, 1, x_113);
lean_inc(x_137);
lean_inc(x_105);
x_138 = l_Lean_Syntax_node3(x_105, x_134, x_136, x_103, x_137);
lean_inc(x_106);
lean_inc(x_105);
x_139 = l_Lean_Syntax_node1(x_105, x_106, x_138);
lean_inc(x_106);
lean_inc(x_105);
x_140 = l_Lean_Syntax_node1(x_105, x_106, x_139);
x_141 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_105);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_105);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_116);
lean_inc(x_55);
lean_inc(x_54);
x_144 = l_Lean_Name_mkStr4(x_54, x_55, x_116, x_143);
x_145 = lean_mk_string_unchecked("Functor.map", 11, 11);
x_146 = l_String_toSubstring_x27(x_145);
x_147 = lean_mk_string_unchecked("Functor", 7, 7);
x_148 = lean_mk_string_unchecked("map", 3, 3);
x_149 = l_Lean_Name_mkStr2(x_147, x_148);
lean_inc(x_107);
lean_inc(x_149);
lean_inc(x_104);
x_150 = l_Lean_addMacroScope(x_104, x_149, x_107);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_inc(x_105);
x_155 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_155, 0, x_105);
lean_ctor_set(x_155, 1, x_146);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_mk_string_unchecked("paren", 5, 5);
lean_inc(x_116);
lean_inc(x_55);
lean_inc(x_54);
x_157 = l_Lean_Name_mkStr4(x_54, x_55, x_116, x_156);
lean_inc(x_105);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_105);
lean_ctor_set(x_158, 1, x_118);
x_159 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_116);
lean_inc(x_55);
lean_inc(x_54);
x_160 = l_Lean_Name_mkStr4(x_54, x_55, x_116, x_159);
x_161 = lean_mk_string_unchecked("@", 1, 1);
lean_inc(x_105);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_105);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_mk_string_unchecked("TSyntax.raw", 11, 11);
x_164 = l_String_toSubstring_x27(x_163);
x_165 = lean_mk_string_unchecked("TSyntax", 7, 7);
x_166 = lean_mk_string_unchecked("raw", 3, 3);
lean_inc(x_166);
lean_inc(x_165);
x_167 = l_Lean_Name_mkStr2(x_165, x_166);
x_168 = l_Lean_addMacroScope(x_104, x_167, x_107);
lean_inc(x_54);
x_169 = l_Lean_Name_mkStr3(x_54, x_165, x_166);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_151);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_153);
lean_inc(x_105);
x_172 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_172, 0, x_105);
lean_ctor_set(x_172, 1, x_164);
lean_ctor_set(x_172, 2, x_168);
lean_ctor_set(x_172, 3, x_171);
lean_inc(x_105);
x_173 = l_Lean_Syntax_node2(x_105, x_160, x_162, x_172);
x_174 = l_Lean_Syntax_getId(x_117);
lean_dec(x_117);
x_175 = lean_erase_macro_scopes(x_174);
lean_inc(x_175);
x_176 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_151, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
lean_dec(x_116);
lean_dec(x_55);
lean_dec(x_54);
x_177 = l_Lean_quoteNameMk(x_175);
x_18 = x_124;
x_19 = x_101;
x_20 = x_105;
x_21 = x_109;
x_22 = x_114;
x_23 = x_155;
x_24 = x_137;
x_25 = x_142;
x_26 = x_123;
x_27 = x_100;
x_28 = x_102;
x_29 = x_106;
x_30 = x_126;
x_31 = x_130;
x_32 = x_108;
x_33 = x_144;
x_34 = x_140;
x_35 = x_111;
x_36 = x_158;
x_37 = x_173;
x_38 = x_125;
x_39 = x_128;
x_40 = x_119;
x_41 = x_132;
x_42 = x_157;
x_43 = x_177;
goto block_53;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_mk_string_unchecked("quotedName", 10, 10);
x_180 = l_Lean_Name_mkStr4(x_54, x_55, x_116, x_179);
x_181 = lean_mk_string_unchecked("`", 1, 1);
x_182 = lean_mk_string_unchecked(".", 1, 1);
x_183 = l_String_intercalate(x_182, x_178);
lean_dec(x_182);
x_184 = lean_string_append(x_181, x_183);
lean_dec(x_183);
lean_inc(x_108);
x_185 = l_Lean_Syntax_mkNameLit(x_184, x_108);
x_186 = lean_mk_empty_array_with_capacity(x_110);
x_187 = lean_array_push(x_186, x_185);
lean_inc(x_108);
x_188 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_188, 0, x_108);
lean_ctor_set(x_188, 1, x_180);
lean_ctor_set(x_188, 2, x_187);
x_18 = x_124;
x_19 = x_101;
x_20 = x_105;
x_21 = x_109;
x_22 = x_114;
x_23 = x_155;
x_24 = x_137;
x_25 = x_142;
x_26 = x_123;
x_27 = x_100;
x_28 = x_102;
x_29 = x_106;
x_30 = x_126;
x_31 = x_130;
x_32 = x_108;
x_33 = x_144;
x_34 = x_140;
x_35 = x_111;
x_36 = x_158;
x_37 = x_173;
x_38 = x_125;
x_39 = x_128;
x_40 = x_119;
x_41 = x_132;
x_42 = x_157;
x_43 = x_188;
goto block_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacro_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_elabMacro_spec__0(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabMacro___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabMacro(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacro__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("macro", 5, 5);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("elabMacro", 9, 9);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacro___boxed), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacro_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("elabMacro", 9, 9);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(14u);
x_8 = lean_unsigned_to_nat(50u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(44u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(54u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(63u);
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
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Macro(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_MacroArgUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMacro__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabMacro_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
