// Lean compiler output
// Module: Lean.Elab.Tactic.SimpTrace
// Imports: Lean.Elab.ElabRules Lean.Elab.Tactic.Simp Lean.Meta.Tactic.TryThis
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Syntax_unsetTrailing(x_1);
x_9 = l_Lean_Elab_Tactic_mkSimpOnly(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_mkSimpCallStx(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty(lean_box(0));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_mk_empty_array_with_capacity(x_2);
x_17 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_3);
x_18 = l_Lean_Elab_Tactic_simpLocation(x_4, x_5, x_6, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_Elab_Tactic_expandLocation(x_19);
x_21 = l_Lean_Elab_Tactic_simpLocation(x_4, x_5, x_6, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (x_1 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_570; uint8_t x_571; 
x_18 = lean_unsigned_to_nat(0u);
x_509 = lean_unsigned_to_nat(1u);
x_570 = l_Lean_Syntax_getArg(x_7, x_509);
x_571 = l_Lean_Syntax_isNone(x_570);
if (x_571 == 0)
{
uint8_t x_572; 
lean_inc(x_570);
x_572 = l_Lean_Syntax_matchesNull(x_570, x_509);
if (x_572 == 0)
{
lean_object* x_573; 
lean_dec(x_570);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_573 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_16);
return x_573;
}
else
{
lean_object* x_574; lean_object* x_575; 
x_574 = l_Lean_Syntax_getArg(x_570, x_18);
lean_dec(x_570);
x_575 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_575, 0, x_574);
x_540 = x_575;
x_541 = x_8;
x_542 = x_9;
x_543 = x_10;
x_544 = x_11;
x_545 = x_12;
x_546 = x_13;
x_547 = x_14;
x_548 = x_15;
x_549 = x_16;
goto block_569;
}
}
else
{
lean_object* x_576; 
lean_dec(x_570);
x_576 = lean_box(0);
x_540 = x_576;
x_541 = x_8;
x_542 = x_9;
x_543 = x_10;
x_544 = x_11;
x_545 = x_12;
x_546 = x_13;
x_547 = x_14;
x_548 = x_15;
x_549 = x_16;
goto block_569;
}
block_73:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_box(x_2);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(x_35, 0, x_20);
lean_closure_set(x_35, 1, x_18);
lean_closure_set(x_35, 2, x_34);
lean_closure_set(x_35, 3, x_33);
lean_closure_set(x_35, 4, x_21);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_36 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_19, x_35, x_30, x_32, x_22, x_28, x_23, x_26, x_29, x_31, x_27);
lean_dec(x_19);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_26);
lean_inc(x_23);
x_40 = l_Lean_Elab_Tactic_mkSimpCallStx(x_24, x_39, x_23, x_26, x_29, x_31, x_38);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_29, 5);
lean_inc(x_43);
x_44 = lean_mk_string_unchecked("tactic", 6, 6);
x_45 = l_Lean_Name_mkStr1(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
x_47 = lean_box(0);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_49);
lean_ctor_set(x_51, 5, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_43);
x_53 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_54 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_25, x_51, x_52, x_53, x_47, x_23, x_26, x_29, x_31, x_42);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_52);
lean_dec(x_25);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_dec(x_37);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_ctor_get(x_37, 1);
lean_inc(x_59);
lean_dec(x_37);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_37);
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_37);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
x_65 = !lean_is_exclusive(x_40);
if (x_65 == 0)
{
return x_40;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_40, 0);
x_67 = lean_ctor_get(x_40, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_40);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_69 = !lean_is_exclusive(x_36);
if (x_69 == 0)
{
return x_36;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_36, 0);
x_71 = lean_ctor_get(x_36, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_36);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_113:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; 
x_88 = lean_box(0);
x_89 = lean_box(0);
x_90 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_91 = lean_unbox(x_88);
x_92 = lean_unbox(x_89);
x_93 = lean_unbox(x_88);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
x_94 = l_Lean_Elab_Tactic_mkSimpContext(x_78, x_91, x_92, x_93, x_90, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 2);
lean_inc(x_99);
lean_dec(x_95);
x_19 = x_99;
x_20 = x_74;
x_21 = x_98;
x_22 = x_81;
x_23 = x_83;
x_24 = x_78;
x_25 = x_75;
x_26 = x_84;
x_27 = x_96;
x_28 = x_82;
x_29 = x_85;
x_30 = x_79;
x_31 = x_86;
x_32 = x_80;
x_33 = x_97;
goto block_73;
}
else
{
lean_dec(x_77);
if (x_76 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_95, 2);
lean_inc(x_103);
lean_dec(x_95);
x_19 = x_103;
x_20 = x_74;
x_21 = x_102;
x_22 = x_81;
x_23 = x_83;
x_24 = x_78;
x_25 = x_75;
x_26 = x_84;
x_27 = x_100;
x_28 = x_82;
x_29 = x_85;
x_30 = x_79;
x_31 = x_86;
x_32 = x_80;
x_33 = x_101;
goto block_73;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
lean_dec(x_94);
x_105 = lean_ctor_get(x_95, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_95, 2);
lean_inc(x_107);
lean_dec(x_95);
x_108 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_105);
lean_dec(x_105);
x_19 = x_107;
x_20 = x_74;
x_21 = x_106;
x_22 = x_81;
x_23 = x_83;
x_24 = x_78;
x_25 = x_75;
x_26 = x_84;
x_27 = x_104;
x_28 = x_82;
x_29 = x_85;
x_30 = x_79;
x_31 = x_86;
x_32 = x_80;
x_33 = x_108;
goto block_73;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
x_109 = !lean_is_exclusive(x_94);
if (x_109 == 0)
{
return x_94;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_94, 0);
x_111 = lean_ctor_get(x_94, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_94);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_140:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l_Array_append(lean_box(0), x_117, x_136);
lean_dec(x_136);
lean_inc(x_131);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_131);
lean_ctor_set(x_138, 1, x_123);
lean_ctor_set(x_138, 2, x_137);
x_139 = l_Lean_Syntax_node6(x_131, x_135, x_124, x_127, x_128, x_115, x_129, x_138);
x_74 = x_114;
x_75 = x_116;
x_76 = x_130;
x_77 = x_119;
x_78 = x_139;
x_79 = x_133;
x_80 = x_126;
x_81 = x_132;
x_82 = x_122;
x_83 = x_134;
x_84 = x_121;
x_85 = x_118;
x_86 = x_120;
x_87 = x_125;
goto block_113;
}
block_170:
{
lean_object* x_164; lean_object* x_165; 
lean_inc(x_143);
x_164 = l_Array_append(lean_box(0), x_143, x_163);
lean_dec(x_163);
lean_inc(x_150);
lean_inc(x_158);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_158);
lean_ctor_set(x_165, 1, x_150);
lean_ctor_set(x_165, 2, x_164);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_166; 
x_166 = l_Array_empty(lean_box(0));
x_114 = x_141;
x_115 = x_142;
x_116 = x_144;
x_117 = x_143;
x_118 = x_145;
x_119 = x_146;
x_120 = x_147;
x_121 = x_148;
x_122 = x_149;
x_123 = x_150;
x_124 = x_151;
x_125 = x_152;
x_126 = x_153;
x_127 = x_154;
x_128 = x_155;
x_129 = x_165;
x_130 = x_157;
x_131 = x_158;
x_132 = x_156;
x_133 = x_159;
x_134 = x_161;
x_135 = x_162;
x_136 = x_166;
goto block_140;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_160, 0);
lean_inc(x_167);
lean_dec(x_160);
x_168 = l_Array_empty(lean_box(0));
x_169 = lean_array_push(x_168, x_167);
x_114 = x_141;
x_115 = x_142;
x_116 = x_144;
x_117 = x_143;
x_118 = x_145;
x_119 = x_146;
x_120 = x_147;
x_121 = x_148;
x_122 = x_149;
x_123 = x_150;
x_124 = x_151;
x_125 = x_152;
x_126 = x_153;
x_127 = x_154;
x_128 = x_155;
x_129 = x_165;
x_130 = x_157;
x_131 = x_158;
x_132 = x_156;
x_133 = x_159;
x_134 = x_161;
x_135 = x_162;
x_136 = x_169;
goto block_140;
}
}
block_205:
{
lean_object* x_194; lean_object* x_195; 
lean_inc(x_172);
x_194 = l_Array_append(lean_box(0), x_172, x_193);
lean_dec(x_193);
lean_inc(x_180);
lean_inc(x_188);
x_195 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_195, 0, x_188);
lean_ctor_set(x_195, 1, x_180);
lean_ctor_set(x_195, 2, x_194);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_196; 
x_196 = l_Array_empty(lean_box(0));
x_141 = x_171;
x_142 = x_195;
x_143 = x_172;
x_144 = x_173;
x_145 = x_175;
x_146 = x_176;
x_147 = x_177;
x_148 = x_178;
x_149 = x_179;
x_150 = x_180;
x_151 = x_181;
x_152 = x_182;
x_153 = x_183;
x_154 = x_184;
x_155 = x_185;
x_156 = x_187;
x_157 = x_186;
x_158 = x_188;
x_159 = x_189;
x_160 = x_190;
x_161 = x_191;
x_162 = x_192;
x_163 = x_196;
goto block_170;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_197 = lean_ctor_get(x_174, 0);
lean_inc(x_197);
lean_dec(x_174);
x_198 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_188);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_198);
lean_inc(x_172);
x_200 = l_Array_append(lean_box(0), x_172, x_197);
lean_dec(x_197);
lean_inc(x_180);
lean_inc(x_188);
x_201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_201, 0, x_188);
lean_ctor_set(x_201, 1, x_180);
lean_ctor_set(x_201, 2, x_200);
x_202 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_188);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_188);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Array_mkArray3(lean_box(0), x_199, x_201, x_203);
x_141 = x_171;
x_142 = x_195;
x_143 = x_172;
x_144 = x_173;
x_145 = x_175;
x_146 = x_176;
x_147 = x_177;
x_148 = x_178;
x_149 = x_179;
x_150 = x_180;
x_151 = x_181;
x_152 = x_182;
x_153 = x_183;
x_154 = x_184;
x_155 = x_185;
x_156 = x_187;
x_157 = x_186;
x_158 = x_188;
x_159 = x_189;
x_160 = x_190;
x_161 = x_191;
x_162 = x_192;
x_163 = x_204;
goto block_170;
}
}
block_237:
{
lean_object* x_229; lean_object* x_230; 
lean_inc(x_207);
x_229 = l_Array_append(lean_box(0), x_207, x_228);
lean_dec(x_228);
lean_inc(x_215);
lean_inc(x_223);
x_230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_215);
lean_ctor_set(x_230, 2, x_229);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_231; 
x_231 = l_Array_empty(lean_box(0));
x_171 = x_206;
x_172 = x_207;
x_173 = x_208;
x_174 = x_209;
x_175 = x_210;
x_176 = x_211;
x_177 = x_212;
x_178 = x_213;
x_179 = x_214;
x_180 = x_215;
x_181 = x_216;
x_182 = x_217;
x_183 = x_218;
x_184 = x_220;
x_185 = x_230;
x_186 = x_222;
x_187 = x_221;
x_188 = x_223;
x_189 = x_224;
x_190 = x_225;
x_191 = x_226;
x_192 = x_227;
x_193 = x_231;
goto block_205;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_219, 0);
lean_inc(x_232);
lean_dec(x_219);
x_233 = l_Lean_SourceInfo_fromRef(x_232, x_2);
lean_dec(x_232);
x_234 = lean_mk_string_unchecked("only", 4, 4);
x_235 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Array_mkArray1___redArg(x_235);
x_171 = x_206;
x_172 = x_207;
x_173 = x_208;
x_174 = x_209;
x_175 = x_210;
x_176 = x_211;
x_177 = x_212;
x_178 = x_213;
x_179 = x_214;
x_180 = x_215;
x_181 = x_216;
x_182 = x_217;
x_183 = x_218;
x_184 = x_220;
x_185 = x_230;
x_186 = x_222;
x_187 = x_221;
x_188 = x_223;
x_189 = x_224;
x_190 = x_225;
x_191 = x_226;
x_192 = x_227;
x_193 = x_236;
goto block_205;
}
}
block_285:
{
lean_object* x_257; uint8_t x_258; 
x_257 = lean_st_ref_get(x_245, x_243);
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_259 = lean_ctor_get(x_257, 1);
x_260 = lean_ctor_get(x_257, 0);
lean_dec(x_260);
x_261 = lean_ctor_get(x_241, 5);
lean_inc(x_261);
x_262 = l_Lean_SourceInfo_fromRef(x_261, x_256);
lean_dec(x_261);
x_263 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_263);
x_264 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_263);
x_265 = l_Lean_SourceInfo_fromRef(x_240, x_2);
lean_ctor_set_tag(x_257, 2);
lean_ctor_set(x_257, 1, x_263);
lean_ctor_set(x_257, 0, x_265);
x_266 = lean_mk_string_unchecked("null", 4, 4);
x_267 = l_Lean_Name_mkStr1(x_266);
x_268 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_269; 
x_269 = l_Array_empty(lean_box(0));
x_206 = x_238;
x_207 = x_268;
x_208 = x_240;
x_209 = x_242;
x_210 = x_241;
x_211 = x_244;
x_212 = x_245;
x_213 = x_246;
x_214 = x_247;
x_215 = x_267;
x_216 = x_257;
x_217 = x_259;
x_218 = x_248;
x_219 = x_249;
x_220 = x_250;
x_221 = x_251;
x_222 = x_252;
x_223 = x_262;
x_224 = x_253;
x_225 = x_254;
x_226 = x_255;
x_227 = x_264;
x_228 = x_269;
goto block_237;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_239, 0);
lean_inc(x_270);
lean_dec(x_239);
x_271 = l_Array_mkArray1___redArg(x_270);
x_206 = x_238;
x_207 = x_268;
x_208 = x_240;
x_209 = x_242;
x_210 = x_241;
x_211 = x_244;
x_212 = x_245;
x_213 = x_246;
x_214 = x_247;
x_215 = x_267;
x_216 = x_257;
x_217 = x_259;
x_218 = x_248;
x_219 = x_249;
x_220 = x_250;
x_221 = x_251;
x_222 = x_252;
x_223 = x_262;
x_224 = x_253;
x_225 = x_254;
x_226 = x_255;
x_227 = x_264;
x_228 = x_271;
goto block_237;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_272 = lean_ctor_get(x_257, 1);
lean_inc(x_272);
lean_dec(x_257);
x_273 = lean_ctor_get(x_241, 5);
lean_inc(x_273);
x_274 = l_Lean_SourceInfo_fromRef(x_273, x_256);
lean_dec(x_273);
x_275 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_275);
x_276 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_275);
x_277 = l_Lean_SourceInfo_fromRef(x_240, x_2);
x_278 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
x_279 = lean_mk_string_unchecked("null", 4, 4);
x_280 = l_Lean_Name_mkStr1(x_279);
x_281 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_282; 
x_282 = l_Array_empty(lean_box(0));
x_206 = x_238;
x_207 = x_281;
x_208 = x_240;
x_209 = x_242;
x_210 = x_241;
x_211 = x_244;
x_212 = x_245;
x_213 = x_246;
x_214 = x_247;
x_215 = x_280;
x_216 = x_278;
x_217 = x_272;
x_218 = x_248;
x_219 = x_249;
x_220 = x_250;
x_221 = x_251;
x_222 = x_252;
x_223 = x_274;
x_224 = x_253;
x_225 = x_254;
x_226 = x_255;
x_227 = x_276;
x_228 = x_282;
goto block_237;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_239, 0);
lean_inc(x_283);
lean_dec(x_239);
x_284 = l_Array_mkArray1___redArg(x_283);
x_206 = x_238;
x_207 = x_281;
x_208 = x_240;
x_209 = x_242;
x_210 = x_241;
x_211 = x_244;
x_212 = x_245;
x_213 = x_246;
x_214 = x_247;
x_215 = x_280;
x_216 = x_278;
x_217 = x_272;
x_218 = x_248;
x_219 = x_249;
x_220 = x_250;
x_221 = x_251;
x_222 = x_252;
x_223 = x_274;
x_224 = x_253;
x_225 = x_254;
x_226 = x_255;
x_227 = x_276;
x_228 = x_284;
goto block_237;
}
}
}
block_312:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = l_Array_append(lean_box(0), x_305, x_308);
lean_dec(x_308);
lean_inc(x_287);
x_310 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_310, 0, x_287);
lean_ctor_set(x_310, 1, x_291);
lean_ctor_set(x_310, 2, x_309);
x_311 = l_Lean_Syntax_node6(x_287, x_298, x_290, x_300, x_306, x_301, x_288, x_310);
x_74 = x_286;
x_75 = x_289;
x_76 = x_302;
x_77 = x_294;
x_78 = x_311;
x_79 = x_304;
x_80 = x_299;
x_81 = x_303;
x_82 = x_297;
x_83 = x_307;
x_84 = x_296;
x_85 = x_292;
x_86 = x_295;
x_87 = x_293;
goto block_113;
}
block_341:
{
lean_object* x_336; lean_object* x_337; 
lean_inc(x_332);
x_336 = l_Array_append(lean_box(0), x_332, x_335);
lean_dec(x_335);
lean_inc(x_317);
lean_inc(x_314);
x_337 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_337, 0, x_314);
lean_ctor_set(x_337, 1, x_317);
lean_ctor_set(x_337, 2, x_336);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_338; 
lean_dec(x_6);
x_338 = l_Array_empty(lean_box(0));
x_286 = x_313;
x_287 = x_314;
x_288 = x_337;
x_289 = x_315;
x_290 = x_316;
x_291 = x_317;
x_292 = x_318;
x_293 = x_319;
x_294 = x_320;
x_295 = x_321;
x_296 = x_322;
x_297 = x_323;
x_298 = x_324;
x_299 = x_325;
x_300 = x_326;
x_301 = x_327;
x_302 = x_329;
x_303 = x_328;
x_304 = x_330;
x_305 = x_332;
x_306 = x_333;
x_307 = x_334;
x_308 = x_338;
goto block_312;
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_331, 0);
lean_inc(x_339);
lean_dec(x_331);
x_340 = lean_apply_1(x_6, x_339);
x_286 = x_313;
x_287 = x_314;
x_288 = x_337;
x_289 = x_315;
x_290 = x_316;
x_291 = x_317;
x_292 = x_318;
x_293 = x_319;
x_294 = x_320;
x_295 = x_321;
x_296 = x_322;
x_297 = x_323;
x_298 = x_324;
x_299 = x_325;
x_300 = x_326;
x_301 = x_327;
x_302 = x_329;
x_303 = x_328;
x_304 = x_330;
x_305 = x_332;
x_306 = x_333;
x_307 = x_334;
x_308 = x_340;
goto block_312;
}
}
block_376:
{
lean_object* x_365; lean_object* x_366; 
lean_inc(x_361);
x_365 = l_Array_append(lean_box(0), x_361, x_364);
lean_dec(x_364);
lean_inc(x_346);
lean_inc(x_343);
x_366 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_366, 0, x_343);
lean_ctor_set(x_366, 1, x_346);
lean_ctor_set(x_366, 2, x_365);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_367; 
x_367 = l_Array_empty(lean_box(0));
x_313 = x_342;
x_314 = x_343;
x_315 = x_344;
x_316 = x_345;
x_317 = x_346;
x_318 = x_348;
x_319 = x_349;
x_320 = x_350;
x_321 = x_351;
x_322 = x_352;
x_323 = x_353;
x_324 = x_354;
x_325 = x_355;
x_326 = x_356;
x_327 = x_366;
x_328 = x_358;
x_329 = x_357;
x_330 = x_359;
x_331 = x_360;
x_332 = x_361;
x_333 = x_362;
x_334 = x_363;
x_335 = x_367;
goto block_341;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_368 = lean_ctor_get(x_347, 0);
lean_inc(x_368);
lean_dec(x_347);
x_369 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_343);
x_370 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_370, 0, x_343);
lean_ctor_set(x_370, 1, x_369);
lean_inc(x_361);
x_371 = l_Array_append(lean_box(0), x_361, x_368);
lean_dec(x_368);
lean_inc(x_346);
lean_inc(x_343);
x_372 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_372, 0, x_343);
lean_ctor_set(x_372, 1, x_346);
lean_ctor_set(x_372, 2, x_371);
x_373 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_343);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_343);
lean_ctor_set(x_374, 1, x_373);
x_375 = l_Array_mkArray3(lean_box(0), x_370, x_372, x_374);
x_313 = x_342;
x_314 = x_343;
x_315 = x_344;
x_316 = x_345;
x_317 = x_346;
x_318 = x_348;
x_319 = x_349;
x_320 = x_350;
x_321 = x_351;
x_322 = x_352;
x_323 = x_353;
x_324 = x_354;
x_325 = x_355;
x_326 = x_356;
x_327 = x_366;
x_328 = x_358;
x_329 = x_357;
x_330 = x_359;
x_331 = x_360;
x_332 = x_361;
x_333 = x_362;
x_334 = x_363;
x_335 = x_375;
goto block_341;
}
}
block_408:
{
lean_object* x_400; lean_object* x_401; 
lean_inc(x_397);
x_400 = l_Array_append(lean_box(0), x_397, x_399);
lean_dec(x_399);
lean_inc(x_381);
lean_inc(x_378);
x_401 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_401, 0, x_378);
lean_ctor_set(x_401, 1, x_381);
lean_ctor_set(x_401, 2, x_400);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_402; 
x_402 = l_Array_empty(lean_box(0));
x_342 = x_377;
x_343 = x_378;
x_344 = x_379;
x_345 = x_380;
x_346 = x_381;
x_347 = x_382;
x_348 = x_383;
x_349 = x_384;
x_350 = x_385;
x_351 = x_386;
x_352 = x_387;
x_353 = x_388;
x_354 = x_390;
x_355 = x_389;
x_356 = x_392;
x_357 = x_394;
x_358 = x_393;
x_359 = x_395;
x_360 = x_396;
x_361 = x_397;
x_362 = x_401;
x_363 = x_398;
x_364 = x_402;
goto block_376;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_403 = lean_ctor_get(x_391, 0);
lean_inc(x_403);
lean_dec(x_391);
x_404 = l_Lean_SourceInfo_fromRef(x_403, x_2);
lean_dec(x_403);
x_405 = lean_mk_string_unchecked("only", 4, 4);
x_406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_Array_mkArray1___redArg(x_406);
x_342 = x_377;
x_343 = x_378;
x_344 = x_379;
x_345 = x_380;
x_346 = x_381;
x_347 = x_382;
x_348 = x_383;
x_349 = x_384;
x_350 = x_385;
x_351 = x_386;
x_352 = x_387;
x_353 = x_388;
x_354 = x_390;
x_355 = x_389;
x_356 = x_392;
x_357 = x_394;
x_358 = x_393;
x_359 = x_395;
x_360 = x_396;
x_361 = x_397;
x_362 = x_401;
x_363 = x_398;
x_364 = x_407;
goto block_376;
}
}
block_462:
{
lean_object* x_425; 
x_425 = l_Lean_Syntax_getArg(x_7, x_18);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_426; uint8_t x_427; 
lean_dec(x_6);
x_426 = lean_box(0);
x_427 = lean_unbox(x_426);
lean_inc(x_413);
x_238 = x_413;
x_239 = x_424;
x_240 = x_425;
x_241 = x_410;
x_242 = x_420;
x_243 = x_418;
x_244 = x_419;
x_245 = x_421;
x_246 = x_412;
x_247 = x_411;
x_248 = x_415;
x_249 = x_422;
x_250 = x_423;
x_251 = x_414;
x_252 = x_409;
x_253 = x_416;
x_254 = x_413;
x_255 = x_417;
x_256 = x_427;
goto block_285;
}
else
{
if (x_409 == 0)
{
lean_dec(x_6);
lean_inc(x_413);
x_238 = x_413;
x_239 = x_424;
x_240 = x_425;
x_241 = x_410;
x_242 = x_420;
x_243 = x_418;
x_244 = x_419;
x_245 = x_421;
x_246 = x_412;
x_247 = x_411;
x_248 = x_415;
x_249 = x_422;
x_250 = x_423;
x_251 = x_414;
x_252 = x_409;
x_253 = x_416;
x_254 = x_413;
x_255 = x_417;
x_256 = x_409;
goto block_285;
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = lean_st_ref_get(x_421, x_418);
x_429 = !lean_is_exclusive(x_428);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_430 = lean_ctor_get(x_428, 1);
x_431 = lean_ctor_get(x_428, 0);
lean_dec(x_431);
x_432 = lean_ctor_get(x_410, 5);
lean_inc(x_432);
x_433 = lean_box(0);
x_434 = lean_unbox(x_433);
x_435 = l_Lean_SourceInfo_fromRef(x_432, x_434);
lean_dec(x_432);
x_436 = lean_mk_string_unchecked("simpAutoUnfold", 14, 14);
x_437 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_436);
x_438 = l_Lean_SourceInfo_fromRef(x_425, x_2);
x_439 = lean_mk_string_unchecked("simp!", 5, 5);
lean_ctor_set_tag(x_428, 2);
lean_ctor_set(x_428, 1, x_439);
lean_ctor_set(x_428, 0, x_438);
x_440 = lean_mk_string_unchecked("null", 4, 4);
x_441 = l_Lean_Name_mkStr1(x_440);
x_442 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_443; 
x_443 = l_Array_empty(lean_box(0));
lean_inc(x_413);
x_377 = x_413;
x_378 = x_435;
x_379 = x_425;
x_380 = x_428;
x_381 = x_441;
x_382 = x_420;
x_383 = x_410;
x_384 = x_430;
x_385 = x_419;
x_386 = x_421;
x_387 = x_412;
x_388 = x_411;
x_389 = x_415;
x_390 = x_437;
x_391 = x_422;
x_392 = x_423;
x_393 = x_414;
x_394 = x_409;
x_395 = x_416;
x_396 = x_413;
x_397 = x_442;
x_398 = x_417;
x_399 = x_443;
goto block_408;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_424, 0);
lean_inc(x_444);
lean_dec(x_424);
lean_inc(x_6);
x_445 = lean_apply_1(x_6, x_444);
lean_inc(x_413);
x_377 = x_413;
x_378 = x_435;
x_379 = x_425;
x_380 = x_428;
x_381 = x_441;
x_382 = x_420;
x_383 = x_410;
x_384 = x_430;
x_385 = x_419;
x_386 = x_421;
x_387 = x_412;
x_388 = x_411;
x_389 = x_415;
x_390 = x_437;
x_391 = x_422;
x_392 = x_423;
x_393 = x_414;
x_394 = x_409;
x_395 = x_416;
x_396 = x_413;
x_397 = x_442;
x_398 = x_417;
x_399 = x_445;
goto block_408;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_428, 1);
lean_inc(x_446);
lean_dec(x_428);
x_447 = lean_ctor_get(x_410, 5);
lean_inc(x_447);
x_448 = lean_box(0);
x_449 = lean_unbox(x_448);
x_450 = l_Lean_SourceInfo_fromRef(x_447, x_449);
lean_dec(x_447);
x_451 = lean_mk_string_unchecked("simpAutoUnfold", 14, 14);
x_452 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_451);
x_453 = l_Lean_SourceInfo_fromRef(x_425, x_2);
x_454 = lean_mk_string_unchecked("simp!", 5, 5);
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_mk_string_unchecked("null", 4, 4);
x_457 = l_Lean_Name_mkStr1(x_456);
x_458 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_459; 
x_459 = l_Array_empty(lean_box(0));
lean_inc(x_413);
x_377 = x_413;
x_378 = x_450;
x_379 = x_425;
x_380 = x_455;
x_381 = x_457;
x_382 = x_420;
x_383 = x_410;
x_384 = x_446;
x_385 = x_419;
x_386 = x_421;
x_387 = x_412;
x_388 = x_411;
x_389 = x_415;
x_390 = x_452;
x_391 = x_422;
x_392 = x_423;
x_393 = x_414;
x_394 = x_409;
x_395 = x_416;
x_396 = x_413;
x_397 = x_458;
x_398 = x_417;
x_399 = x_459;
goto block_408;
}
else
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_ctor_get(x_424, 0);
lean_inc(x_460);
lean_dec(x_424);
lean_inc(x_6);
x_461 = lean_apply_1(x_6, x_460);
lean_inc(x_413);
x_377 = x_413;
x_378 = x_450;
x_379 = x_425;
x_380 = x_455;
x_381 = x_457;
x_382 = x_420;
x_383 = x_410;
x_384 = x_446;
x_385 = x_419;
x_386 = x_421;
x_387 = x_412;
x_388 = x_411;
x_389 = x_415;
x_390 = x_452;
x_391 = x_422;
x_392 = x_423;
x_393 = x_414;
x_394 = x_409;
x_395 = x_416;
x_396 = x_413;
x_397 = x_458;
x_398 = x_417;
x_399 = x_461;
goto block_408;
}
}
}
}
}
block_484:
{
lean_object* x_479; 
x_479 = l_Lean_Syntax_getOptional_x3f(x_463);
lean_dec(x_463);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; 
x_480 = lean_box(0);
x_409 = x_474;
x_410 = x_464;
x_411 = x_470;
x_412 = x_469;
x_413 = x_478;
x_414 = x_475;
x_415 = x_471;
x_416 = x_476;
x_417 = x_477;
x_418 = x_467;
x_419 = x_466;
x_420 = x_465;
x_421 = x_468;
x_422 = x_472;
x_423 = x_473;
x_424 = x_480;
goto block_462;
}
else
{
uint8_t x_481; 
x_481 = !lean_is_exclusive(x_479);
if (x_481 == 0)
{
x_409 = x_474;
x_410 = x_464;
x_411 = x_470;
x_412 = x_469;
x_413 = x_478;
x_414 = x_475;
x_415 = x_471;
x_416 = x_476;
x_417 = x_477;
x_418 = x_467;
x_419 = x_466;
x_420 = x_465;
x_421 = x_468;
x_422 = x_472;
x_423 = x_473;
x_424 = x_479;
goto block_462;
}
else
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_ctor_get(x_479, 0);
lean_inc(x_482);
lean_dec(x_479);
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_409 = x_474;
x_410 = x_464;
x_411 = x_470;
x_412 = x_469;
x_413 = x_478;
x_414 = x_475;
x_415 = x_471;
x_416 = x_476;
x_417 = x_477;
x_418 = x_467;
x_419 = x_466;
x_420 = x_465;
x_421 = x_468;
x_422 = x_472;
x_423 = x_473;
x_424 = x_483;
goto block_462;
}
}
}
block_508:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_unsigned_to_nat(4u);
x_502 = l_Lean_Syntax_getArg(x_489, x_501);
lean_dec(x_489);
x_503 = l_Lean_Syntax_getOptional_x3f(x_502);
lean_dec(x_502);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; 
x_504 = lean_box(0);
x_463 = x_485;
x_464 = x_498;
x_465 = x_491;
x_466 = x_490;
x_467 = x_500;
x_468 = x_499;
x_469 = x_497;
x_470 = x_495;
x_471 = x_493;
x_472 = x_486;
x_473 = x_487;
x_474 = x_488;
x_475 = x_494;
x_476 = x_492;
x_477 = x_496;
x_478 = x_504;
goto block_484;
}
else
{
uint8_t x_505; 
x_505 = !lean_is_exclusive(x_503);
if (x_505 == 0)
{
x_463 = x_485;
x_464 = x_498;
x_465 = x_491;
x_466 = x_490;
x_467 = x_500;
x_468 = x_499;
x_469 = x_497;
x_470 = x_495;
x_471 = x_493;
x_472 = x_486;
x_473 = x_487;
x_474 = x_488;
x_475 = x_494;
x_476 = x_492;
x_477 = x_496;
x_478 = x_503;
goto block_484;
}
else
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_ctor_get(x_503, 0);
lean_inc(x_506);
lean_dec(x_503);
x_507 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_507, 0, x_506);
x_463 = x_485;
x_464 = x_498;
x_465 = x_491;
x_466 = x_490;
x_467 = x_500;
x_468 = x_499;
x_469 = x_497;
x_470 = x_495;
x_471 = x_493;
x_472 = x_486;
x_473 = x_487;
x_474 = x_488;
x_475 = x_494;
x_476 = x_492;
x_477 = x_496;
x_478 = x_507;
goto block_484;
}
}
}
block_539:
{
lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_525 = lean_unsigned_to_nat(3u);
x_526 = l_Lean_Syntax_getArg(x_514, x_525);
x_527 = l_Lean_Syntax_isNone(x_526);
if (x_527 == 0)
{
uint8_t x_528; 
lean_inc(x_526);
x_528 = l_Lean_Syntax_matchesNull(x_526, x_509);
if (x_528 == 0)
{
lean_object* x_529; 
lean_dec(x_526);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_529 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_524);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_530 = l_Lean_Syntax_getArg(x_526, x_18);
lean_dec(x_526);
x_531 = lean_mk_string_unchecked("simpArgs", 8, 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_532 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_531);
lean_inc(x_530);
x_533 = l_Lean_Syntax_isOfKind(x_530, x_532);
lean_dec(x_532);
if (x_533 == 0)
{
lean_object* x_534; 
lean_dec(x_530);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_534 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_524);
return x_534;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = l_Lean_Syntax_getArg(x_530, x_509);
lean_dec(x_530);
x_536 = l_Lean_Syntax_getArgs(x_535);
lean_dec(x_535);
x_537 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_537, 0, x_536);
x_485 = x_510;
x_486 = x_515;
x_487 = x_511;
x_488 = x_512;
x_489 = x_514;
x_490 = x_513;
x_491 = x_537;
x_492 = x_516;
x_493 = x_517;
x_494 = x_518;
x_495 = x_519;
x_496 = x_520;
x_497 = x_521;
x_498 = x_522;
x_499 = x_523;
x_500 = x_524;
goto block_508;
}
}
}
else
{
lean_object* x_538; 
lean_dec(x_526);
x_538 = lean_box(0);
x_485 = x_510;
x_486 = x_515;
x_487 = x_511;
x_488 = x_512;
x_489 = x_514;
x_490 = x_513;
x_491 = x_538;
x_492 = x_516;
x_493 = x_517;
x_494 = x_518;
x_495 = x_519;
x_496 = x_520;
x_497 = x_521;
x_498 = x_522;
x_499 = x_523;
x_500 = x_524;
goto block_508;
}
}
block_569:
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; 
x_550 = lean_unsigned_to_nat(2u);
x_551 = l_Lean_Syntax_getArg(x_7, x_550);
x_552 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_553 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_552);
lean_inc(x_551);
x_554 = l_Lean_Syntax_isOfKind(x_551, x_553);
lean_dec(x_553);
if (x_554 == 0)
{
lean_object* x_555; 
lean_dec(x_551);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_555 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_549);
return x_555;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_556 = l_Lean_Syntax_getArg(x_551, x_18);
x_557 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_558 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_557);
lean_inc(x_556);
x_559 = l_Lean_Syntax_isOfKind(x_556, x_558);
lean_dec(x_558);
if (x_559 == 0)
{
lean_object* x_560; 
lean_dec(x_556);
lean_dec(x_551);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_560 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_549);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; uint8_t x_563; 
x_561 = l_Lean_Syntax_getArg(x_551, x_509);
x_562 = l_Lean_Syntax_getArg(x_551, x_550);
x_563 = l_Lean_Syntax_isNone(x_562);
if (x_563 == 0)
{
uint8_t x_564; 
lean_inc(x_562);
x_564 = l_Lean_Syntax_matchesNull(x_562, x_509);
if (x_564 == 0)
{
lean_object* x_565; 
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_556);
lean_dec(x_551);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_565 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_549);
return x_565;
}
else
{
lean_object* x_566; lean_object* x_567; 
x_566 = l_Lean_Syntax_getArg(x_562, x_18);
lean_dec(x_562);
x_567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_567, 0, x_566);
x_510 = x_561;
x_511 = x_556;
x_512 = x_559;
x_513 = x_540;
x_514 = x_551;
x_515 = x_567;
x_516 = x_541;
x_517 = x_542;
x_518 = x_543;
x_519 = x_544;
x_520 = x_545;
x_521 = x_546;
x_522 = x_547;
x_523 = x_548;
x_524 = x_549;
goto block_539;
}
}
else
{
lean_object* x_568; 
lean_dec(x_562);
x_568 = lean_box(0);
x_510 = x_561;
x_511 = x_556;
x_512 = x_559;
x_513 = x_540;
x_514 = x_551;
x_515 = x_568;
x_516 = x_541;
x_517 = x_542;
x_518 = x_543;
x_519 = x_544;
x_520 = x_545;
x_521 = x_546;
x_522 = x_547;
x_523 = x_548;
x_524 = x_549;
goto block_539;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__0), 1, 0);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_box(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_12);
lean_closure_set(x_20, 3, x_13);
lean_closure_set(x_20, 4, x_14);
lean_closure_set(x_20, 5, x_11);
lean_closure_set(x_20, 6, x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_Tactic_withMainContext___redArg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpTrace", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimpTrace", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalSimpTrace", 13, 13);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(25u);
x_8 = lean_unsigned_to_nat(28u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(40u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(45u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
if (x_1 == 0)
{
lean_object* x_55; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_536; uint8_t x_537; 
x_56 = lean_unsigned_to_nat(0u);
x_474 = lean_unsigned_to_nat(1u);
x_536 = l_Lean_Syntax_getArg(x_6, x_474);
x_537 = l_Lean_Syntax_isNone(x_536);
if (x_537 == 0)
{
uint8_t x_538; 
lean_inc(x_536);
x_538 = l_Lean_Syntax_matchesNull(x_536, x_474);
if (x_538 == 0)
{
lean_object* x_539; 
lean_dec(x_536);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_539 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; 
x_540 = l_Lean_Syntax_getArg(x_536, x_56);
lean_dec(x_536);
x_541 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_541, 0, x_540);
x_506 = x_541;
x_507 = x_7;
x_508 = x_8;
x_509 = x_9;
x_510 = x_10;
x_511 = x_11;
x_512 = x_12;
x_513 = x_13;
x_514 = x_14;
x_515 = x_15;
goto block_535;
}
}
else
{
lean_object* x_542; 
lean_dec(x_536);
x_542 = lean_box(0);
x_506 = x_542;
x_507 = x_7;
x_508 = x_8;
x_509 = x_9;
x_510 = x_10;
x_511 = x_11;
x_512 = x_12;
x_513 = x_13;
x_514 = x_14;
x_515 = x_15;
goto block_535;
}
block_131:
{
lean_object* x_70; 
x_70 = l_Lean_Elab_Tactic_getMainGoal(x_62, x_61, x_68, x_63, x_58, x_65, x_67, x_64, x_59);
lean_dec(x_63);
lean_dec(x_68);
lean_dec(x_62);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_mk_empty_array_with_capacity(x_56);
x_74 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_74);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_inc(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_56);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_74);
x_78 = lean_unsigned_to_nat(5u);
x_79 = lean_usize_of_nat(x_78);
x_80 = lean_usize_to_nat(x_79);
x_81 = lean_nat_pow(x_66, x_80);
lean_dec(x_80);
x_82 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_83 = lean_usize_to_nat(x_82);
x_84 = lean_mk_empty_array_with_capacity(x_83);
lean_dec(x_83);
lean_inc(x_84);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_56);
lean_ctor_set(x_86, 3, x_56);
lean_ctor_set_usize(x_86, 4, x_79);
lean_inc(x_75);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_75);
lean_ctor_set(x_87, 1, x_75);
lean_ctor_set(x_87, 2, x_77);
lean_ctor_set(x_87, 3, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_64);
lean_inc(x_67);
lean_inc(x_65);
x_89 = l_Lean_Meta_simpAll(x_71, x_69, x_73, x_88, x_58, x_65, x_67, x_64, x_72);
lean_dec(x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_box(0);
x_95 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_94, x_61, x_58, x_65, x_67, x_64, x_92);
lean_dec(x_61);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_16 = x_57;
x_17 = x_60;
x_18 = x_93;
x_19 = x_58;
x_20 = x_65;
x_21 = x_67;
x_22 = x_64;
x_23 = x_96;
goto block_54;
}
else
{
uint8_t x_97; 
lean_dec(x_93);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_95);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
lean_dec(x_89);
x_102 = !lean_is_exclusive(x_90);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_90, 1);
x_104 = lean_ctor_get(x_90, 0);
lean_dec(x_104);
x_105 = lean_ctor_get(x_91, 0);
lean_inc(x_105);
lean_dec(x_91);
x_106 = lean_box(0);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_106);
lean_ctor_set(x_90, 0, x_105);
x_107 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_90, x_61, x_58, x_65, x_67, x_64, x_101);
lean_dec(x_61);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_16 = x_57;
x_17 = x_60;
x_18 = x_103;
x_19 = x_58;
x_20 = x_65;
x_21 = x_67;
x_22 = x_64;
x_23 = x_108;
goto block_54;
}
else
{
uint8_t x_109; 
lean_dec(x_103);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
return x_107;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_107);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_90, 1);
lean_inc(x_113);
lean_dec(x_90);
x_114 = lean_ctor_get(x_91, 0);
lean_inc(x_114);
lean_dec(x_91);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_116, x_61, x_58, x_65, x_67, x_64, x_101);
lean_dec(x_61);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_16 = x_57;
x_17 = x_60;
x_18 = x_113;
x_19 = x_58;
x_20 = x_65;
x_21 = x_67;
x_22 = x_64;
x_23 = x_118;
goto block_54;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
x_123 = !lean_is_exclusive(x_89);
if (x_123 == 0)
{
return x_89;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_89, 0);
x_125 = lean_ctor_get(x_89, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_89);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
x_127 = !lean_is_exclusive(x_70);
if (x_127 == 0)
{
return x_70;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_70, 0);
x_129 = lean_ctor_get(x_70, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_70);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
block_162:
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_146 = lean_box(1);
x_147 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
x_148 = lean_unbox(x_146);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
x_149 = l_Lean_Elab_Tactic_mkSimpContext(x_136, x_2, x_148, x_2, x_147, x_137, x_138, x_139, x_140, x_141, x_142, x_143, x_144, x_145);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_57 = x_136;
x_58 = x_141;
x_59 = x_151;
x_60 = x_133;
x_61 = x_138;
x_62 = x_137;
x_63 = x_140;
x_64 = x_144;
x_65 = x_142;
x_66 = x_135;
x_67 = x_143;
x_68 = x_139;
x_69 = x_152;
goto block_131;
}
else
{
lean_dec(x_134);
if (x_132 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_149, 1);
lean_inc(x_153);
lean_dec(x_149);
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
lean_dec(x_150);
x_57 = x_136;
x_58 = x_141;
x_59 = x_153;
x_60 = x_133;
x_61 = x_138;
x_62 = x_137;
x_63 = x_140;
x_64 = x_144;
x_65 = x_142;
x_66 = x_135;
x_67 = x_143;
x_68 = x_139;
x_69 = x_154;
goto block_131;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
lean_dec(x_149);
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
lean_dec(x_150);
x_157 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_156);
lean_dec(x_156);
x_57 = x_136;
x_58 = x_141;
x_59 = x_155;
x_60 = x_133;
x_61 = x_138;
x_62 = x_137;
x_63 = x_140;
x_64 = x_144;
x_65 = x_142;
x_66 = x_135;
x_67 = x_143;
x_68 = x_139;
x_69 = x_157;
goto block_131;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
x_158 = !lean_is_exclusive(x_149);
if (x_158 == 0)
{
return x_149;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_149, 0);
x_160 = lean_ctor_get(x_149, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_149);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
block_188:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = l_Array_append(lean_box(0), x_183, x_184);
lean_dec(x_184);
lean_inc(x_169);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_169);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_185);
x_187 = l_Lean_Syntax_node5(x_169, x_179, x_163, x_170, x_171, x_178, x_186);
x_132 = x_175;
x_133 = x_174;
x_134 = x_180;
x_135 = x_168;
x_136 = x_187;
x_137 = x_173;
x_138 = x_166;
x_139 = x_176;
x_140 = x_177;
x_141 = x_167;
x_142 = x_172;
x_143 = x_181;
x_144 = x_164;
x_145 = x_165;
goto block_162;
}
block_222:
{
lean_object* x_211; lean_object* x_212; 
lean_inc(x_209);
x_211 = l_Array_append(lean_box(0), x_209, x_210);
lean_dec(x_210);
lean_inc(x_208);
lean_inc(x_195);
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_195);
lean_ctor_set(x_212, 1, x_208);
lean_ctor_set(x_212, 2, x_211);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_213; 
x_213 = l_Array_empty(lean_box(0));
x_163 = x_189;
x_164 = x_190;
x_165 = x_191;
x_166 = x_192;
x_167 = x_193;
x_168 = x_194;
x_169 = x_195;
x_170 = x_196;
x_171 = x_197;
x_172 = x_198;
x_173 = x_199;
x_174 = x_204;
x_175 = x_203;
x_176 = x_202;
x_177 = x_201;
x_178 = x_212;
x_179 = x_205;
x_180 = x_206;
x_181 = x_207;
x_182 = x_208;
x_183 = x_209;
x_184 = x_213;
goto block_188;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_214 = lean_ctor_get(x_200, 0);
lean_inc(x_214);
lean_dec(x_200);
x_215 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_195);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_195);
lean_ctor_set(x_216, 1, x_215);
lean_inc(x_209);
x_217 = l_Array_append(lean_box(0), x_209, x_214);
lean_dec(x_214);
lean_inc(x_208);
lean_inc(x_195);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_195);
lean_ctor_set(x_218, 1, x_208);
lean_ctor_set(x_218, 2, x_217);
x_219 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_195);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_195);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Array_mkArray3(lean_box(0), x_216, x_218, x_220);
x_163 = x_189;
x_164 = x_190;
x_165 = x_191;
x_166 = x_192;
x_167 = x_193;
x_168 = x_194;
x_169 = x_195;
x_170 = x_196;
x_171 = x_197;
x_172 = x_198;
x_173 = x_199;
x_174 = x_204;
x_175 = x_203;
x_176 = x_202;
x_177 = x_201;
x_178 = x_212;
x_179 = x_205;
x_180 = x_206;
x_181 = x_207;
x_182 = x_208;
x_183 = x_209;
x_184 = x_221;
goto block_188;
}
}
block_253:
{
lean_object* x_245; lean_object* x_246; 
lean_inc(x_243);
x_245 = l_Array_append(lean_box(0), x_243, x_244);
lean_dec(x_244);
lean_inc(x_242);
lean_inc(x_229);
x_246 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_246, 0, x_229);
lean_ctor_set(x_246, 1, x_242);
lean_ctor_set(x_246, 2, x_245);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_247; 
x_247 = l_Array_empty(lean_box(0));
x_189 = x_223;
x_190 = x_224;
x_191 = x_225;
x_192 = x_226;
x_193 = x_227;
x_194 = x_228;
x_195 = x_229;
x_196 = x_230;
x_197 = x_246;
x_198 = x_231;
x_199 = x_232;
x_200 = x_233;
x_201 = x_237;
x_202 = x_236;
x_203 = x_235;
x_204 = x_234;
x_205 = x_238;
x_206 = x_239;
x_207 = x_241;
x_208 = x_242;
x_209 = x_243;
x_210 = x_247;
goto block_222;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_240, 0);
lean_inc(x_248);
lean_dec(x_240);
x_249 = l_Lean_SourceInfo_fromRef(x_248, x_2);
lean_dec(x_248);
x_250 = lean_mk_string_unchecked("only", 4, 4);
x_251 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Array_mkArray1___redArg(x_251);
x_189 = x_223;
x_190 = x_224;
x_191 = x_225;
x_192 = x_226;
x_193 = x_227;
x_194 = x_228;
x_195 = x_229;
x_196 = x_230;
x_197 = x_246;
x_198 = x_231;
x_199 = x_232;
x_200 = x_233;
x_201 = x_237;
x_202 = x_236;
x_203 = x_235;
x_204 = x_234;
x_205 = x_238;
x_206 = x_239;
x_207 = x_241;
x_208 = x_242;
x_209 = x_243;
x_210 = x_252;
goto block_222;
}
}
block_304:
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_st_ref_get(x_254, x_267);
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_274 = lean_ctor_get(x_272, 1);
x_275 = lean_ctor_get(x_272, 0);
lean_dec(x_275);
x_276 = lean_ctor_get(x_270, 5);
lean_inc(x_276);
x_277 = l_Lean_SourceInfo_fromRef(x_276, x_271);
lean_dec(x_276);
x_278 = lean_mk_string_unchecked("simpAll", 7, 7);
x_279 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_278);
x_280 = l_Lean_SourceInfo_fromRef(x_264, x_2);
x_281 = lean_mk_string_unchecked("simp_all", 8, 8);
lean_ctor_set_tag(x_272, 2);
lean_ctor_set(x_272, 1, x_281);
lean_ctor_set(x_272, 0, x_280);
x_282 = lean_mk_string_unchecked("null", 4, 4);
x_283 = l_Lean_Name_mkStr1(x_282);
x_284 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_285; 
x_285 = l_Array_empty(lean_box(0));
x_223 = x_272;
x_224 = x_254;
x_225 = x_274;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_277;
x_230 = x_258;
x_231 = x_260;
x_232 = x_261;
x_233 = x_262;
x_234 = x_264;
x_235 = x_265;
x_236 = x_266;
x_237 = x_263;
x_238 = x_279;
x_239 = x_268;
x_240 = x_269;
x_241 = x_270;
x_242 = x_283;
x_243 = x_284;
x_244 = x_285;
goto block_253;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_259, 0);
lean_inc(x_286);
lean_dec(x_259);
x_287 = l_Array_empty(lean_box(0));
x_288 = lean_array_push(x_287, x_286);
x_223 = x_272;
x_224 = x_254;
x_225 = x_274;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_277;
x_230 = x_258;
x_231 = x_260;
x_232 = x_261;
x_233 = x_262;
x_234 = x_264;
x_235 = x_265;
x_236 = x_266;
x_237 = x_263;
x_238 = x_279;
x_239 = x_268;
x_240 = x_269;
x_241 = x_270;
x_242 = x_283;
x_243 = x_284;
x_244 = x_288;
goto block_253;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_289 = lean_ctor_get(x_272, 1);
lean_inc(x_289);
lean_dec(x_272);
x_290 = lean_ctor_get(x_270, 5);
lean_inc(x_290);
x_291 = l_Lean_SourceInfo_fromRef(x_290, x_271);
lean_dec(x_290);
x_292 = lean_mk_string_unchecked("simpAll", 7, 7);
x_293 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_292);
x_294 = l_Lean_SourceInfo_fromRef(x_264, x_2);
x_295 = lean_mk_string_unchecked("simp_all", 8, 8);
x_296 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_mk_string_unchecked("null", 4, 4);
x_298 = l_Lean_Name_mkStr1(x_297);
x_299 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_300; 
x_300 = l_Array_empty(lean_box(0));
x_223 = x_296;
x_224 = x_254;
x_225 = x_289;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_291;
x_230 = x_258;
x_231 = x_260;
x_232 = x_261;
x_233 = x_262;
x_234 = x_264;
x_235 = x_265;
x_236 = x_266;
x_237 = x_263;
x_238 = x_293;
x_239 = x_268;
x_240 = x_269;
x_241 = x_270;
x_242 = x_298;
x_243 = x_299;
x_244 = x_300;
goto block_253;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_259, 0);
lean_inc(x_301);
lean_dec(x_259);
x_302 = l_Array_empty(lean_box(0));
x_303 = lean_array_push(x_302, x_301);
x_223 = x_296;
x_224 = x_254;
x_225 = x_289;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_291;
x_230 = x_258;
x_231 = x_260;
x_232 = x_261;
x_233 = x_262;
x_234 = x_264;
x_235 = x_265;
x_236 = x_266;
x_237 = x_263;
x_238 = x_293;
x_239 = x_268;
x_240 = x_269;
x_241 = x_270;
x_242 = x_298;
x_243 = x_299;
x_244 = x_303;
goto block_253;
}
}
}
block_330:
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = l_Array_append(lean_box(0), x_311, x_326);
lean_dec(x_326);
lean_inc(x_321);
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_321);
lean_ctor_set(x_328, 1, x_324);
lean_ctor_set(x_328, 2, x_327);
x_329 = l_Lean_Syntax_node5(x_321, x_322, x_320, x_312, x_306, x_325, x_328);
x_132 = x_316;
x_133 = x_315;
x_134 = x_319;
x_135 = x_310;
x_136 = x_329;
x_137 = x_314;
x_138 = x_308;
x_139 = x_317;
x_140 = x_318;
x_141 = x_309;
x_142 = x_313;
x_143 = x_323;
x_144 = x_305;
x_145 = x_307;
goto block_162;
}
block_364:
{
lean_object* x_353; lean_object* x_354; 
lean_inc(x_337);
x_353 = l_Array_append(lean_box(0), x_337, x_352);
lean_dec(x_352);
lean_inc(x_351);
lean_inc(x_349);
x_354 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_354, 0, x_349);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_353);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_355; 
x_355 = l_Array_empty(lean_box(0));
x_305 = x_331;
x_306 = x_332;
x_307 = x_333;
x_308 = x_334;
x_309 = x_335;
x_310 = x_336;
x_311 = x_337;
x_312 = x_338;
x_313 = x_339;
x_314 = x_340;
x_315 = x_345;
x_316 = x_344;
x_317 = x_343;
x_318 = x_342;
x_319 = x_347;
x_320 = x_346;
x_321 = x_349;
x_322 = x_348;
x_323 = x_350;
x_324 = x_351;
x_325 = x_354;
x_326 = x_355;
goto block_330;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_356 = lean_ctor_get(x_341, 0);
lean_inc(x_356);
lean_dec(x_341);
x_357 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_349);
x_358 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_358, 0, x_349);
lean_ctor_set(x_358, 1, x_357);
lean_inc(x_337);
x_359 = l_Array_append(lean_box(0), x_337, x_356);
lean_dec(x_356);
lean_inc(x_351);
lean_inc(x_349);
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_349);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_359);
x_361 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_349);
x_362 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_362, 0, x_349);
lean_ctor_set(x_362, 1, x_361);
x_363 = l_Array_mkArray3(lean_box(0), x_358, x_360, x_362);
x_305 = x_331;
x_306 = x_332;
x_307 = x_333;
x_308 = x_334;
x_309 = x_335;
x_310 = x_336;
x_311 = x_337;
x_312 = x_338;
x_313 = x_339;
x_314 = x_340;
x_315 = x_345;
x_316 = x_344;
x_317 = x_343;
x_318 = x_342;
x_319 = x_347;
x_320 = x_346;
x_321 = x_349;
x_322 = x_348;
x_323 = x_350;
x_324 = x_351;
x_325 = x_354;
x_326 = x_363;
goto block_330;
}
}
block_395:
{
lean_object* x_387; lean_object* x_388; 
lean_inc(x_370);
x_387 = l_Array_append(lean_box(0), x_370, x_386);
lean_dec(x_386);
lean_inc(x_385);
lean_inc(x_383);
x_388 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_388, 0, x_383);
lean_ctor_set(x_388, 1, x_385);
lean_ctor_set(x_388, 2, x_387);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_389; 
x_389 = l_Array_empty(lean_box(0));
x_331 = x_365;
x_332 = x_388;
x_333 = x_366;
x_334 = x_367;
x_335 = x_368;
x_336 = x_369;
x_337 = x_370;
x_338 = x_371;
x_339 = x_372;
x_340 = x_373;
x_341 = x_374;
x_342 = x_378;
x_343 = x_377;
x_344 = x_376;
x_345 = x_375;
x_346 = x_380;
x_347 = x_379;
x_348 = x_382;
x_349 = x_383;
x_350 = x_384;
x_351 = x_385;
x_352 = x_389;
goto block_364;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_390 = lean_ctor_get(x_381, 0);
lean_inc(x_390);
lean_dec(x_381);
x_391 = l_Lean_SourceInfo_fromRef(x_390, x_2);
lean_dec(x_390);
x_392 = lean_mk_string_unchecked("only", 4, 4);
x_393 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = l_Array_mkArray1___redArg(x_393);
x_331 = x_365;
x_332 = x_388;
x_333 = x_366;
x_334 = x_367;
x_335 = x_368;
x_336 = x_369;
x_337 = x_370;
x_338 = x_371;
x_339 = x_372;
x_340 = x_373;
x_341 = x_374;
x_342 = x_378;
x_343 = x_377;
x_344 = x_376;
x_345 = x_375;
x_346 = x_380;
x_347 = x_379;
x_348 = x_382;
x_349 = x_383;
x_350 = x_384;
x_351 = x_385;
x_352 = x_394;
goto block_364;
}
}
block_451:
{
lean_object* x_412; 
x_412 = l_Lean_Syntax_getArg(x_6, x_56);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_413; uint8_t x_414; 
x_413 = lean_box(0);
x_414 = lean_unbox(x_413);
x_254 = x_396;
x_255 = x_397;
x_256 = x_398;
x_257 = x_399;
x_258 = x_400;
x_259 = x_411;
x_260 = x_401;
x_261 = x_402;
x_262 = x_403;
x_263 = x_405;
x_264 = x_412;
x_265 = x_404;
x_266 = x_406;
x_267 = x_407;
x_268 = x_408;
x_269 = x_409;
x_270 = x_410;
x_271 = x_414;
goto block_304;
}
else
{
if (x_404 == 0)
{
x_254 = x_396;
x_255 = x_397;
x_256 = x_398;
x_257 = x_399;
x_258 = x_400;
x_259 = x_411;
x_260 = x_401;
x_261 = x_402;
x_262 = x_403;
x_263 = x_405;
x_264 = x_412;
x_265 = x_404;
x_266 = x_406;
x_267 = x_407;
x_268 = x_408;
x_269 = x_409;
x_270 = x_410;
x_271 = x_404;
goto block_304;
}
else
{
lean_object* x_415; uint8_t x_416; 
x_415 = lean_st_ref_get(x_396, x_407);
x_416 = !lean_is_exclusive(x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_417 = lean_ctor_get(x_415, 1);
x_418 = lean_ctor_get(x_415, 0);
lean_dec(x_418);
x_419 = lean_ctor_get(x_410, 5);
lean_inc(x_419);
x_420 = lean_box(0);
x_421 = lean_unbox(x_420);
x_422 = l_Lean_SourceInfo_fromRef(x_419, x_421);
lean_dec(x_419);
x_423 = lean_mk_string_unchecked("simpAllAutoUnfold", 17, 17);
x_424 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_423);
x_425 = l_Lean_SourceInfo_fromRef(x_412, x_2);
x_426 = lean_mk_string_unchecked("simp_all!", 9, 9);
lean_ctor_set_tag(x_415, 2);
lean_ctor_set(x_415, 1, x_426);
lean_ctor_set(x_415, 0, x_425);
x_427 = lean_mk_string_unchecked("null", 4, 4);
x_428 = l_Lean_Name_mkStr1(x_427);
x_429 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_430; 
x_430 = l_Array_empty(lean_box(0));
x_365 = x_396;
x_366 = x_417;
x_367 = x_397;
x_368 = x_398;
x_369 = x_399;
x_370 = x_429;
x_371 = x_400;
x_372 = x_401;
x_373 = x_402;
x_374 = x_403;
x_375 = x_412;
x_376 = x_404;
x_377 = x_406;
x_378 = x_405;
x_379 = x_408;
x_380 = x_415;
x_381 = x_409;
x_382 = x_424;
x_383 = x_422;
x_384 = x_410;
x_385 = x_428;
x_386 = x_430;
goto block_395;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_411, 0);
lean_inc(x_431);
lean_dec(x_411);
x_432 = l_Array_empty(lean_box(0));
x_433 = lean_array_push(x_432, x_431);
x_365 = x_396;
x_366 = x_417;
x_367 = x_397;
x_368 = x_398;
x_369 = x_399;
x_370 = x_429;
x_371 = x_400;
x_372 = x_401;
x_373 = x_402;
x_374 = x_403;
x_375 = x_412;
x_376 = x_404;
x_377 = x_406;
x_378 = x_405;
x_379 = x_408;
x_380 = x_415;
x_381 = x_409;
x_382 = x_424;
x_383 = x_422;
x_384 = x_410;
x_385 = x_428;
x_386 = x_433;
goto block_395;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_434 = lean_ctor_get(x_415, 1);
lean_inc(x_434);
lean_dec(x_415);
x_435 = lean_ctor_get(x_410, 5);
lean_inc(x_435);
x_436 = lean_box(0);
x_437 = lean_unbox(x_436);
x_438 = l_Lean_SourceInfo_fromRef(x_435, x_437);
lean_dec(x_435);
x_439 = lean_mk_string_unchecked("simpAllAutoUnfold", 17, 17);
x_440 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_439);
x_441 = l_Lean_SourceInfo_fromRef(x_412, x_2);
x_442 = lean_mk_string_unchecked("simp_all!", 9, 9);
x_443 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_mk_string_unchecked("null", 4, 4);
x_445 = l_Lean_Name_mkStr1(x_444);
x_446 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_447; 
x_447 = l_Array_empty(lean_box(0));
x_365 = x_396;
x_366 = x_434;
x_367 = x_397;
x_368 = x_398;
x_369 = x_399;
x_370 = x_446;
x_371 = x_400;
x_372 = x_401;
x_373 = x_402;
x_374 = x_403;
x_375 = x_412;
x_376 = x_404;
x_377 = x_406;
x_378 = x_405;
x_379 = x_408;
x_380 = x_443;
x_381 = x_409;
x_382 = x_440;
x_383 = x_438;
x_384 = x_410;
x_385 = x_445;
x_386 = x_447;
goto block_395;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_411, 0);
lean_inc(x_448);
lean_dec(x_411);
x_449 = l_Array_empty(lean_box(0));
x_450 = lean_array_push(x_449, x_448);
x_365 = x_396;
x_366 = x_434;
x_367 = x_397;
x_368 = x_398;
x_369 = x_399;
x_370 = x_446;
x_371 = x_400;
x_372 = x_401;
x_373 = x_402;
x_374 = x_403;
x_375 = x_412;
x_376 = x_404;
x_377 = x_406;
x_378 = x_405;
x_379 = x_408;
x_380 = x_443;
x_381 = x_409;
x_382 = x_440;
x_383 = x_438;
x_384 = x_410;
x_385 = x_445;
x_386 = x_450;
goto block_395;
}
}
}
}
}
block_473:
{
lean_object* x_468; 
x_468 = l_Lean_Syntax_getOptional_x3f(x_457);
lean_dec(x_457);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; 
x_469 = lean_box(0);
x_396 = x_466;
x_397 = x_460;
x_398 = x_463;
x_399 = x_455;
x_400 = x_456;
x_401 = x_464;
x_402 = x_459;
x_403 = x_458;
x_404 = x_452;
x_405 = x_462;
x_406 = x_461;
x_407 = x_467;
x_408 = x_453;
x_409 = x_454;
x_410 = x_465;
x_411 = x_469;
goto block_451;
}
else
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_468);
if (x_470 == 0)
{
x_396 = x_466;
x_397 = x_460;
x_398 = x_463;
x_399 = x_455;
x_400 = x_456;
x_401 = x_464;
x_402 = x_459;
x_403 = x_458;
x_404 = x_452;
x_405 = x_462;
x_406 = x_461;
x_407 = x_467;
x_408 = x_453;
x_409 = x_454;
x_410 = x_465;
x_411 = x_468;
goto block_451;
}
else
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_ctor_get(x_468, 0);
lean_inc(x_471);
lean_dec(x_468);
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_471);
x_396 = x_466;
x_397 = x_460;
x_398 = x_463;
x_399 = x_455;
x_400 = x_456;
x_401 = x_464;
x_402 = x_459;
x_403 = x_458;
x_404 = x_452;
x_405 = x_462;
x_406 = x_461;
x_407 = x_467;
x_408 = x_453;
x_409 = x_454;
x_410 = x_465;
x_411 = x_472;
goto block_451;
}
}
}
block_505:
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_491 = lean_unsigned_to_nat(3u);
x_492 = l_Lean_Syntax_getArg(x_476, x_491);
lean_dec(x_476);
x_493 = l_Lean_Syntax_isNone(x_492);
if (x_493 == 0)
{
uint8_t x_494; 
lean_inc(x_492);
x_494 = l_Lean_Syntax_matchesNull(x_492, x_474);
if (x_494 == 0)
{
lean_object* x_495; 
lean_dec(x_492);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_495 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_490);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_496 = l_Lean_Syntax_getArg(x_492, x_56);
lean_dec(x_492);
x_497 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_498 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_497);
lean_inc(x_496);
x_499 = l_Lean_Syntax_isOfKind(x_496, x_498);
lean_dec(x_498);
if (x_499 == 0)
{
lean_object* x_500; 
lean_dec(x_496);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_500 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_490);
return x_500;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = l_Lean_Syntax_getArg(x_496, x_474);
lean_dec(x_496);
x_502 = l_Lean_Syntax_getArgs(x_501);
lean_dec(x_501);
x_503 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_503, 0, x_502);
x_452 = x_475;
x_453 = x_477;
x_454 = x_481;
x_455 = x_478;
x_456 = x_479;
x_457 = x_480;
x_458 = x_503;
x_459 = x_482;
x_460 = x_483;
x_461 = x_484;
x_462 = x_485;
x_463 = x_486;
x_464 = x_487;
x_465 = x_488;
x_466 = x_489;
x_467 = x_490;
goto block_473;
}
}
}
else
{
lean_object* x_504; 
lean_dec(x_492);
x_504 = lean_box(0);
x_452 = x_475;
x_453 = x_477;
x_454 = x_481;
x_455 = x_478;
x_456 = x_479;
x_457 = x_480;
x_458 = x_504;
x_459 = x_482;
x_460 = x_483;
x_461 = x_484;
x_462 = x_485;
x_463 = x_486;
x_464 = x_487;
x_465 = x_488;
x_466 = x_489;
x_467 = x_490;
goto block_473;
}
}
block_535:
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_516 = lean_unsigned_to_nat(2u);
x_517 = l_Lean_Syntax_getArg(x_6, x_516);
x_518 = lean_mk_string_unchecked("simpAllTraceArgsRest", 20, 20);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_519 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_518);
lean_inc(x_517);
x_520 = l_Lean_Syntax_isOfKind(x_517, x_519);
lean_dec(x_519);
if (x_520 == 0)
{
lean_object* x_521; 
lean_dec(x_517);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_521 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_515);
return x_521;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_525; 
x_522 = l_Lean_Syntax_getArg(x_517, x_56);
x_523 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_524 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_523);
lean_inc(x_522);
x_525 = l_Lean_Syntax_isOfKind(x_522, x_524);
lean_dec(x_524);
if (x_525 == 0)
{
lean_object* x_526; 
lean_dec(x_522);
lean_dec(x_517);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_526 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_515);
return x_526;
}
else
{
lean_object* x_527; lean_object* x_528; uint8_t x_529; 
x_527 = l_Lean_Syntax_getArg(x_517, x_474);
x_528 = l_Lean_Syntax_getArg(x_517, x_516);
x_529 = l_Lean_Syntax_isNone(x_528);
if (x_529 == 0)
{
uint8_t x_530; 
lean_inc(x_528);
x_530 = l_Lean_Syntax_matchesNull(x_528, x_474);
if (x_530 == 0)
{
lean_object* x_531; 
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_522);
lean_dec(x_517);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_531 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_515);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; 
x_532 = l_Lean_Syntax_getArg(x_528, x_56);
lean_dec(x_528);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
x_475 = x_525;
x_476 = x_517;
x_477 = x_506;
x_478 = x_516;
x_479 = x_522;
x_480 = x_527;
x_481 = x_533;
x_482 = x_507;
x_483 = x_508;
x_484 = x_509;
x_485 = x_510;
x_486 = x_511;
x_487 = x_512;
x_488 = x_513;
x_489 = x_514;
x_490 = x_515;
goto block_505;
}
}
else
{
lean_object* x_534; 
lean_dec(x_528);
x_534 = lean_box(0);
x_475 = x_525;
x_476 = x_517;
x_477 = x_506;
x_478 = x_516;
x_479 = x_522;
x_480 = x_527;
x_481 = x_534;
x_482 = x_507;
x_483 = x_508;
x_484 = x_509;
x_485 = x_510;
x_486 = x_511;
x_487 = x_512;
x_488 = x_513;
x_489 = x_514;
x_490 = x_515;
goto block_505;
}
}
}
}
}
block_54:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_25 = l_Lean_Elab_Tactic_mkSimpCallStx(x_16, x_24, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_21, 5);
lean_inc(x_28);
x_29 = lean_mk_string_unchecked("tactic", 6, 6);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_34);
lean_ctor_set(x_36, 5, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_28);
x_38 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_39 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_17, x_36, x_37, x_38, x_32, x_19, x_20, x_21, x_22, x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_37);
lean_dec(x_17);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_dec(x_18);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_dec(x_18);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_18);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
return x_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("simpAllTrace", 12, 12);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(1);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___boxed), 15, 6);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_11);
lean_closure_set(x_19, 3, x_12);
lean_closure_set(x_19, 4, x_13);
lean_closure_set(x_19, 5, x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = l_Lean_Elab_Tactic_withMainContext___redArg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpAllTrace", 12, 12);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimpAllTrace", 16, 16);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalSimpAllTrace", 16, 16);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(42u);
x_8 = lean_unsigned_to_nat(31u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(58u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_8);
x_13 = lean_unsigned_to_nat(35u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(51u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_addBuiltinDeclarationRanges(x_6, x_18, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_unsigned_to_nat(5u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_nat_pow(x_22, x_25);
lean_dec(x_25);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = lean_usize_to_nat(x_27);
x_29 = lean_mk_empty_array_with_capacity(x_28);
lean_dec(x_28);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set_usize(x_31, 4, x_24);
lean_inc(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_34 = l_Lean_Meta_dsimpGoal(x_15, x_1, x_2, x_4, x_3, x_33, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_39, x_6, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_38);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_dec(x_34);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_35, 1);
x_52 = lean_ctor_get(x_35, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_36, 0);
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_54);
lean_ctor_set(x_35, 0, x_53);
x_55 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_35, x_6, x_9, x_10, x_11, x_12, x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_51);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_51);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_35, 1);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_36, 0);
lean_inc(x_65);
lean_dec(x_36);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_67, x_6, x_9, x_10, x_11, x_12, x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_64);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
return x_34;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_34, 0);
x_78 = lean_ctor_get(x_34, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_34);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_14);
if (x_80 == 0)
{
return x_14;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_14, 0);
x_82 = lean_ctor_get(x_14, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_14);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_x27_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_MVarId_getNondepPropHyps(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Elab_Tactic_dsimpLocation_x27_go(x_1, x_2, x_16, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_getFVarIds(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_dsimpLocation_x27_go(x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Tactic_withMainContext___redArg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_Elab_Tactic_withMainContext___redArg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
if (x_1 == 0)
{
lean_object* x_68; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_501; uint8_t x_502; 
x_69 = lean_unsigned_to_nat(0u);
x_442 = lean_unsigned_to_nat(1u);
x_501 = l_Lean_Syntax_getArg(x_6, x_442);
x_502 = l_Lean_Syntax_isNone(x_501);
if (x_502 == 0)
{
uint8_t x_503; 
lean_inc(x_501);
x_503 = l_Lean_Syntax_matchesNull(x_501, x_442);
if (x_503 == 0)
{
lean_object* x_504; 
lean_dec(x_501);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_504 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_15);
return x_504;
}
else
{
lean_object* x_505; lean_object* x_506; 
x_505 = l_Lean_Syntax_getArg(x_501, x_69);
lean_dec(x_501);
x_506 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_506, 0, x_505);
x_472 = x_506;
x_473 = x_7;
x_474 = x_8;
x_475 = x_9;
x_476 = x_10;
x_477 = x_11;
x_478 = x_12;
x_479 = x_13;
x_480 = x_14;
x_481 = x_15;
goto block_500;
}
}
else
{
lean_object* x_507; 
lean_dec(x_501);
x_507 = lean_box(0);
x_472 = x_507;
x_473 = x_7;
x_474 = x_8;
x_475 = x_9;
x_476 = x_10;
x_477 = x_11;
x_478 = x_12;
x_479 = x_13;
x_480 = x_14;
x_481 = x_15;
goto block_500;
}
block_88:
{
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_mk_empty_array_with_capacity(x_69);
x_85 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_2);
x_16 = x_70;
x_17 = x_71;
x_18 = x_72;
x_19 = x_73;
x_20 = x_74;
x_21 = x_75;
x_22 = x_77;
x_23 = x_78;
x_24 = x_79;
x_25 = x_80;
x_26 = x_81;
x_27 = x_82;
x_28 = x_83;
x_29 = x_85;
goto block_67;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = l_Lean_Elab_Tactic_expandLocation(x_86);
lean_dec(x_86);
x_16 = x_70;
x_17 = x_71;
x_18 = x_72;
x_19 = x_73;
x_20 = x_74;
x_21 = x_75;
x_22 = x_77;
x_23 = x_78;
x_24 = x_79;
x_25 = x_80;
x_26 = x_81;
x_27 = x_82;
x_28 = x_83;
x_29 = x_87;
goto block_67;
}
}
block_123:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_box(0);
x_104 = lean_box(2);
x_105 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
lean_inc(x_93);
x_106 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_106, 0, x_93);
lean_closure_set(x_106, 1, x_103);
lean_closure_set(x_106, 2, x_104);
lean_closure_set(x_106, 3, x_103);
lean_closure_set(x_106, 4, x_105);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
x_107 = l_Lean_Elab_Tactic_withMainContext___redArg(x_106, x_94, x_95, x_96, x_97, x_98, x_99, x_100, x_101, x_102);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_70 = x_96;
x_71 = x_94;
x_72 = x_97;
x_73 = x_111;
x_74 = x_95;
x_75 = x_93;
x_76 = x_90;
x_77 = x_91;
x_78 = x_98;
x_79 = x_101;
x_80 = x_100;
x_81 = x_109;
x_82 = x_99;
x_83 = x_110;
goto block_88;
}
else
{
lean_dec(x_92);
if (x_89 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_70 = x_96;
x_71 = x_94;
x_72 = x_97;
x_73 = x_114;
x_74 = x_95;
x_75 = x_93;
x_76 = x_90;
x_77 = x_91;
x_78 = x_98;
x_79 = x_101;
x_80 = x_100;
x_81 = x_112;
x_82 = x_99;
x_83 = x_113;
goto block_88;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
lean_dec(x_107);
x_116 = lean_ctor_get(x_108, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_dec(x_108);
x_118 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_116);
lean_dec(x_116);
x_70 = x_96;
x_71 = x_94;
x_72 = x_97;
x_73 = x_117;
x_74 = x_95;
x_75 = x_93;
x_76 = x_90;
x_77 = x_91;
x_78 = x_98;
x_79 = x_101;
x_80 = x_100;
x_81 = x_115;
x_82 = x_99;
x_83 = x_118;
goto block_88;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
x_119 = !lean_is_exclusive(x_107);
if (x_119 == 0)
{
return x_107;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_107, 0);
x_121 = lean_ctor_get(x_107, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_107);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
block_150:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = l_Array_append(lean_box(0), x_132, x_146);
lean_dec(x_146);
lean_inc(x_126);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_126);
lean_ctor_set(x_148, 1, x_144);
lean_ctor_set(x_148, 2, x_147);
x_149 = l_Lean_Syntax_node6(x_126, x_127, x_138, x_143, x_130, x_136, x_139, x_148);
x_89 = x_124;
x_90 = x_129;
x_91 = x_131;
x_92 = x_145;
x_93 = x_149;
x_94 = x_140;
x_95 = x_135;
x_96 = x_141;
x_97 = x_128;
x_98 = x_134;
x_99 = x_137;
x_100 = x_133;
x_101 = x_125;
x_102 = x_142;
goto block_123;
}
block_179:
{
lean_object* x_173; lean_object* x_174; 
lean_inc(x_159);
x_173 = l_Array_append(lean_box(0), x_159, x_172);
lean_dec(x_172);
lean_inc(x_170);
lean_inc(x_153);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_153);
lean_ctor_set(x_174, 1, x_170);
lean_ctor_set(x_174, 2, x_173);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_175; 
x_175 = l_Array_empty(lean_box(0));
x_124 = x_151;
x_125 = x_152;
x_126 = x_153;
x_127 = x_154;
x_128 = x_155;
x_129 = x_156;
x_130 = x_157;
x_131 = x_158;
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = x_164;
x_138 = x_166;
x_139 = x_174;
x_140 = x_165;
x_141 = x_167;
x_142 = x_169;
x_143 = x_168;
x_144 = x_170;
x_145 = x_171;
x_146 = x_175;
goto block_150;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_156, 0);
lean_inc(x_176);
x_177 = l_Array_empty(lean_box(0));
x_178 = lean_array_push(x_177, x_176);
x_124 = x_151;
x_125 = x_152;
x_126 = x_153;
x_127 = x_154;
x_128 = x_155;
x_129 = x_156;
x_130 = x_157;
x_131 = x_158;
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = x_164;
x_138 = x_166;
x_139 = x_174;
x_140 = x_165;
x_141 = x_167;
x_142 = x_169;
x_143 = x_168;
x_144 = x_170;
x_145 = x_171;
x_146 = x_178;
goto block_150;
}
}
block_213:
{
lean_object* x_202; lean_object* x_203; 
lean_inc(x_188);
x_202 = l_Array_append(lean_box(0), x_188, x_201);
lean_dec(x_201);
lean_inc(x_198);
lean_inc(x_182);
x_203 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_202);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_204; 
x_204 = l_Array_empty(lean_box(0));
x_151 = x_180;
x_152 = x_181;
x_153 = x_182;
x_154 = x_183;
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_190;
x_162 = x_191;
x_163 = x_203;
x_164 = x_192;
x_165 = x_194;
x_166 = x_193;
x_167 = x_195;
x_168 = x_197;
x_169 = x_196;
x_170 = x_198;
x_171 = x_200;
x_172 = x_204;
goto block_179;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_205 = lean_ctor_get(x_199, 0);
lean_inc(x_205);
lean_dec(x_199);
x_206 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_182);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_182);
lean_ctor_set(x_207, 1, x_206);
lean_inc(x_188);
x_208 = l_Array_append(lean_box(0), x_188, x_205);
lean_dec(x_205);
lean_inc(x_198);
lean_inc(x_182);
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_182);
lean_ctor_set(x_209, 1, x_198);
lean_ctor_set(x_209, 2, x_208);
x_210 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_182);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_182);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Array_mkArray3(lean_box(0), x_207, x_209, x_211);
x_151 = x_180;
x_152 = x_181;
x_153 = x_182;
x_154 = x_183;
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_190;
x_162 = x_191;
x_163 = x_203;
x_164 = x_192;
x_165 = x_194;
x_166 = x_193;
x_167 = x_195;
x_168 = x_197;
x_169 = x_196;
x_170 = x_198;
x_171 = x_200;
x_172 = x_212;
goto block_179;
}
}
block_267:
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_st_ref_get(x_214, x_216);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_233 = lean_ctor_get(x_231, 1);
x_234 = lean_ctor_get(x_231, 0);
lean_dec(x_234);
x_235 = lean_ctor_get(x_220, 5);
lean_inc(x_235);
x_236 = l_Lean_SourceInfo_fromRef(x_235, x_230);
lean_dec(x_235);
x_237 = lean_mk_string_unchecked("dsimp", 5, 5);
lean_inc(x_237);
x_238 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_237);
x_239 = l_Lean_SourceInfo_fromRef(x_219, x_2);
lean_ctor_set_tag(x_231, 2);
lean_ctor_set(x_231, 1, x_237);
lean_ctor_set(x_231, 0, x_239);
x_240 = lean_mk_string_unchecked("null", 4, 4);
x_241 = l_Lean_Name_mkStr1(x_240);
x_242 = l_Array_mkArray0(lean_box(0));
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_236);
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_236);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set(x_243, 2, x_242);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_244; 
x_244 = l_Array_empty(lean_box(0));
x_180 = x_215;
x_181 = x_214;
x_182 = x_236;
x_183 = x_238;
x_184 = x_217;
x_185 = x_218;
x_186 = x_243;
x_187 = x_219;
x_188 = x_242;
x_189 = x_220;
x_190 = x_221;
x_191 = x_222;
x_192 = x_223;
x_193 = x_231;
x_194 = x_224;
x_195 = x_225;
x_196 = x_233;
x_197 = x_226;
x_198 = x_241;
x_199 = x_228;
x_200 = x_229;
x_201 = x_244;
goto block_213;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_227, 0);
lean_inc(x_245);
lean_dec(x_227);
x_246 = l_Lean_SourceInfo_fromRef(x_245, x_2);
lean_dec(x_245);
x_247 = lean_mk_string_unchecked("only", 4, 4);
x_248 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Array_mkArray1___redArg(x_248);
x_180 = x_215;
x_181 = x_214;
x_182 = x_236;
x_183 = x_238;
x_184 = x_217;
x_185 = x_218;
x_186 = x_243;
x_187 = x_219;
x_188 = x_242;
x_189 = x_220;
x_190 = x_221;
x_191 = x_222;
x_192 = x_223;
x_193 = x_231;
x_194 = x_224;
x_195 = x_225;
x_196 = x_233;
x_197 = x_226;
x_198 = x_241;
x_199 = x_228;
x_200 = x_229;
x_201 = x_249;
goto block_213;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_250 = lean_ctor_get(x_231, 1);
lean_inc(x_250);
lean_dec(x_231);
x_251 = lean_ctor_get(x_220, 5);
lean_inc(x_251);
x_252 = l_Lean_SourceInfo_fromRef(x_251, x_230);
lean_dec(x_251);
x_253 = lean_mk_string_unchecked("dsimp", 5, 5);
lean_inc(x_253);
x_254 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_253);
x_255 = l_Lean_SourceInfo_fromRef(x_219, x_2);
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_253);
x_257 = lean_mk_string_unchecked("null", 4, 4);
x_258 = l_Lean_Name_mkStr1(x_257);
x_259 = l_Array_mkArray0(lean_box(0));
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_252);
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_258);
lean_ctor_set(x_260, 2, x_259);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_261; 
x_261 = l_Array_empty(lean_box(0));
x_180 = x_215;
x_181 = x_214;
x_182 = x_252;
x_183 = x_254;
x_184 = x_217;
x_185 = x_218;
x_186 = x_260;
x_187 = x_219;
x_188 = x_259;
x_189 = x_220;
x_190 = x_221;
x_191 = x_222;
x_192 = x_223;
x_193 = x_256;
x_194 = x_224;
x_195 = x_225;
x_196 = x_250;
x_197 = x_226;
x_198 = x_258;
x_199 = x_228;
x_200 = x_229;
x_201 = x_261;
goto block_213;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_262 = lean_ctor_get(x_227, 0);
lean_inc(x_262);
lean_dec(x_227);
x_263 = l_Lean_SourceInfo_fromRef(x_262, x_2);
lean_dec(x_262);
x_264 = lean_mk_string_unchecked("only", 4, 4);
x_265 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Array_mkArray1___redArg(x_265);
x_180 = x_215;
x_181 = x_214;
x_182 = x_252;
x_183 = x_254;
x_184 = x_217;
x_185 = x_218;
x_186 = x_260;
x_187 = x_219;
x_188 = x_259;
x_189 = x_220;
x_190 = x_221;
x_191 = x_222;
x_192 = x_223;
x_193 = x_256;
x_194 = x_224;
x_195 = x_225;
x_196 = x_250;
x_197 = x_226;
x_198 = x_258;
x_199 = x_228;
x_200 = x_229;
x_201 = x_266;
goto block_213;
}
}
}
block_294:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = l_Array_append(lean_box(0), x_272, x_290);
lean_dec(x_290);
lean_inc(x_286);
x_292 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_292, 0, x_286);
lean_ctor_set(x_292, 1, x_282);
lean_ctor_set(x_292, 2, x_291);
x_293 = l_Lean_Syntax_node6(x_286, x_273, x_277, x_287, x_288, x_270, x_281, x_292);
x_89 = x_268;
x_90 = x_275;
x_91 = x_276;
x_92 = x_289;
x_93 = x_293;
x_94 = x_284;
x_95 = x_280;
x_96 = x_285;
x_97 = x_274;
x_98 = x_279;
x_99 = x_283;
x_100 = x_278;
x_101 = x_269;
x_102 = x_271;
goto block_123;
}
block_323:
{
lean_object* x_317; lean_object* x_318; 
lean_inc(x_298);
x_317 = l_Array_append(lean_box(0), x_298, x_316);
lean_dec(x_316);
lean_inc(x_308);
lean_inc(x_312);
x_318 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_318, 0, x_312);
lean_ctor_set(x_318, 1, x_308);
lean_ctor_set(x_318, 2, x_317);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_319; 
x_319 = l_Array_empty(lean_box(0));
x_268 = x_295;
x_269 = x_296;
x_270 = x_297;
x_271 = x_299;
x_272 = x_298;
x_273 = x_300;
x_274 = x_301;
x_275 = x_302;
x_276 = x_303;
x_277 = x_304;
x_278 = x_307;
x_279 = x_306;
x_280 = x_305;
x_281 = x_318;
x_282 = x_308;
x_283 = x_309;
x_284 = x_310;
x_285 = x_311;
x_286 = x_312;
x_287 = x_313;
x_288 = x_314;
x_289 = x_315;
x_290 = x_319;
goto block_294;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_302, 0);
lean_inc(x_320);
x_321 = l_Array_empty(lean_box(0));
x_322 = lean_array_push(x_321, x_320);
x_268 = x_295;
x_269 = x_296;
x_270 = x_297;
x_271 = x_299;
x_272 = x_298;
x_273 = x_300;
x_274 = x_301;
x_275 = x_302;
x_276 = x_303;
x_277 = x_304;
x_278 = x_307;
x_279 = x_306;
x_280 = x_305;
x_281 = x_318;
x_282 = x_308;
x_283 = x_309;
x_284 = x_310;
x_285 = x_311;
x_286 = x_312;
x_287 = x_313;
x_288 = x_314;
x_289 = x_315;
x_290 = x_322;
goto block_294;
}
}
block_357:
{
lean_object* x_346; lean_object* x_347; 
lean_inc(x_326);
x_346 = l_Array_append(lean_box(0), x_326, x_345);
lean_dec(x_345);
lean_inc(x_336);
lean_inc(x_340);
x_347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_347, 0, x_340);
lean_ctor_set(x_347, 1, x_336);
lean_ctor_set(x_347, 2, x_346);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_348; 
x_348 = l_Array_empty(lean_box(0));
x_295 = x_324;
x_296 = x_325;
x_297 = x_347;
x_298 = x_326;
x_299 = x_327;
x_300 = x_328;
x_301 = x_329;
x_302 = x_330;
x_303 = x_331;
x_304 = x_332;
x_305 = x_334;
x_306 = x_335;
x_307 = x_333;
x_308 = x_336;
x_309 = x_337;
x_310 = x_338;
x_311 = x_339;
x_312 = x_340;
x_313 = x_341;
x_314 = x_342;
x_315 = x_344;
x_316 = x_348;
goto block_323;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_349 = lean_ctor_get(x_343, 0);
lean_inc(x_349);
lean_dec(x_343);
x_350 = lean_mk_string_unchecked("[", 1, 1);
lean_inc(x_340);
x_351 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_351, 0, x_340);
lean_ctor_set(x_351, 1, x_350);
lean_inc(x_326);
x_352 = l_Array_append(lean_box(0), x_326, x_349);
lean_dec(x_349);
lean_inc(x_336);
lean_inc(x_340);
x_353 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_353, 0, x_340);
lean_ctor_set(x_353, 1, x_336);
lean_ctor_set(x_353, 2, x_352);
x_354 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_340);
x_355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_355, 0, x_340);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Array_mkArray3(lean_box(0), x_351, x_353, x_355);
x_295 = x_324;
x_296 = x_325;
x_297 = x_347;
x_298 = x_326;
x_299 = x_327;
x_300 = x_328;
x_301 = x_329;
x_302 = x_330;
x_303 = x_331;
x_304 = x_332;
x_305 = x_334;
x_306 = x_335;
x_307 = x_333;
x_308 = x_336;
x_309 = x_337;
x_310 = x_338;
x_311 = x_339;
x_312 = x_340;
x_313 = x_341;
x_314 = x_342;
x_315 = x_344;
x_316 = x_356;
goto block_323;
}
}
block_418:
{
lean_object* x_373; 
x_373 = l_Lean_Syntax_getArg(x_6, x_69);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_374; uint8_t x_375; 
x_374 = lean_box(0);
x_375 = lean_unbox(x_374);
x_214 = x_359;
x_215 = x_358;
x_216 = x_360;
x_217 = x_361;
x_218 = x_372;
x_219 = x_373;
x_220 = x_362;
x_221 = x_363;
x_222 = x_364;
x_223 = x_365;
x_224 = x_366;
x_225 = x_367;
x_226 = x_368;
x_227 = x_369;
x_228 = x_370;
x_229 = x_371;
x_230 = x_375;
goto block_267;
}
else
{
if (x_358 == 0)
{
x_214 = x_359;
x_215 = x_358;
x_216 = x_360;
x_217 = x_361;
x_218 = x_372;
x_219 = x_373;
x_220 = x_362;
x_221 = x_363;
x_222 = x_364;
x_223 = x_365;
x_224 = x_366;
x_225 = x_367;
x_226 = x_368;
x_227 = x_369;
x_228 = x_370;
x_229 = x_371;
x_230 = x_358;
goto block_267;
}
else
{
lean_object* x_376; uint8_t x_377; 
x_376 = lean_st_ref_get(x_359, x_360);
x_377 = !lean_is_exclusive(x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_378 = lean_ctor_get(x_376, 1);
x_379 = lean_ctor_get(x_376, 0);
lean_dec(x_379);
x_380 = lean_ctor_get(x_362, 5);
lean_inc(x_380);
x_381 = lean_box(0);
x_382 = lean_unbox(x_381);
x_383 = l_Lean_SourceInfo_fromRef(x_380, x_382);
lean_dec(x_380);
x_384 = lean_mk_string_unchecked("dsimpAutoUnfold", 15, 15);
x_385 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_384);
x_386 = l_Lean_SourceInfo_fromRef(x_373, x_2);
x_387 = lean_mk_string_unchecked("dsimp!", 6, 6);
lean_ctor_set_tag(x_376, 2);
lean_ctor_set(x_376, 1, x_387);
lean_ctor_set(x_376, 0, x_386);
x_388 = lean_mk_string_unchecked("null", 4, 4);
x_389 = l_Lean_Name_mkStr1(x_388);
x_390 = l_Array_mkArray0(lean_box(0));
lean_inc(x_390);
lean_inc(x_389);
lean_inc(x_383);
x_391 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_391, 0, x_383);
lean_ctor_set(x_391, 1, x_389);
lean_ctor_set(x_391, 2, x_390);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_392; 
x_392 = l_Array_empty(lean_box(0));
x_324 = x_358;
x_325 = x_359;
x_326 = x_390;
x_327 = x_378;
x_328 = x_385;
x_329 = x_361;
x_330 = x_372;
x_331 = x_373;
x_332 = x_376;
x_333 = x_362;
x_334 = x_364;
x_335 = x_363;
x_336 = x_389;
x_337 = x_365;
x_338 = x_366;
x_339 = x_367;
x_340 = x_383;
x_341 = x_368;
x_342 = x_391;
x_343 = x_370;
x_344 = x_371;
x_345 = x_392;
goto block_357;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_393 = lean_ctor_get(x_369, 0);
lean_inc(x_393);
lean_dec(x_369);
x_394 = l_Lean_SourceInfo_fromRef(x_393, x_2);
lean_dec(x_393);
x_395 = lean_mk_string_unchecked("only", 4, 4);
x_396 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Array_mkArray1___redArg(x_396);
x_324 = x_358;
x_325 = x_359;
x_326 = x_390;
x_327 = x_378;
x_328 = x_385;
x_329 = x_361;
x_330 = x_372;
x_331 = x_373;
x_332 = x_376;
x_333 = x_362;
x_334 = x_364;
x_335 = x_363;
x_336 = x_389;
x_337 = x_365;
x_338 = x_366;
x_339 = x_367;
x_340 = x_383;
x_341 = x_368;
x_342 = x_391;
x_343 = x_370;
x_344 = x_371;
x_345 = x_397;
goto block_357;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_398 = lean_ctor_get(x_376, 1);
lean_inc(x_398);
lean_dec(x_376);
x_399 = lean_ctor_get(x_362, 5);
lean_inc(x_399);
x_400 = lean_box(0);
x_401 = lean_unbox(x_400);
x_402 = l_Lean_SourceInfo_fromRef(x_399, x_401);
lean_dec(x_399);
x_403 = lean_mk_string_unchecked("dsimpAutoUnfold", 15, 15);
x_404 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_403);
x_405 = l_Lean_SourceInfo_fromRef(x_373, x_2);
x_406 = lean_mk_string_unchecked("dsimp!", 6, 6);
x_407 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_mk_string_unchecked("null", 4, 4);
x_409 = l_Lean_Name_mkStr1(x_408);
x_410 = l_Array_mkArray0(lean_box(0));
lean_inc(x_410);
lean_inc(x_409);
lean_inc(x_402);
x_411 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_411, 0, x_402);
lean_ctor_set(x_411, 1, x_409);
lean_ctor_set(x_411, 2, x_410);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_412; 
x_412 = l_Array_empty(lean_box(0));
x_324 = x_358;
x_325 = x_359;
x_326 = x_410;
x_327 = x_398;
x_328 = x_404;
x_329 = x_361;
x_330 = x_372;
x_331 = x_373;
x_332 = x_407;
x_333 = x_362;
x_334 = x_364;
x_335 = x_363;
x_336 = x_409;
x_337 = x_365;
x_338 = x_366;
x_339 = x_367;
x_340 = x_402;
x_341 = x_368;
x_342 = x_411;
x_343 = x_370;
x_344 = x_371;
x_345 = x_412;
goto block_357;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_413 = lean_ctor_get(x_369, 0);
lean_inc(x_413);
lean_dec(x_369);
x_414 = l_Lean_SourceInfo_fromRef(x_413, x_2);
lean_dec(x_413);
x_415 = lean_mk_string_unchecked("only", 4, 4);
x_416 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_417 = l_Array_mkArray1___redArg(x_416);
x_324 = x_358;
x_325 = x_359;
x_326 = x_410;
x_327 = x_398;
x_328 = x_404;
x_329 = x_361;
x_330 = x_372;
x_331 = x_373;
x_332 = x_407;
x_333 = x_362;
x_334 = x_364;
x_335 = x_363;
x_336 = x_409;
x_337 = x_365;
x_338 = x_366;
x_339 = x_367;
x_340 = x_402;
x_341 = x_368;
x_342 = x_411;
x_343 = x_370;
x_344 = x_371;
x_345 = x_417;
goto block_357;
}
}
}
}
}
block_441:
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_unsigned_to_nat(3u);
x_435 = l_Lean_Syntax_getArg(x_420, x_434);
lean_dec(x_420);
x_436 = l_Lean_Syntax_getOptional_x3f(x_435);
lean_dec(x_435);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; 
x_437 = lean_box(0);
x_358 = x_419;
x_359 = x_432;
x_360 = x_433;
x_361 = x_428;
x_362 = x_431;
x_363 = x_429;
x_364 = x_426;
x_365 = x_430;
x_366 = x_425;
x_367 = x_427;
x_368 = x_421;
x_369 = x_422;
x_370 = x_424;
x_371 = x_423;
x_372 = x_437;
goto block_418;
}
else
{
uint8_t x_438; 
x_438 = !lean_is_exclusive(x_436);
if (x_438 == 0)
{
x_358 = x_419;
x_359 = x_432;
x_360 = x_433;
x_361 = x_428;
x_362 = x_431;
x_363 = x_429;
x_364 = x_426;
x_365 = x_430;
x_366 = x_425;
x_367 = x_427;
x_368 = x_421;
x_369 = x_422;
x_370 = x_424;
x_371 = x_423;
x_372 = x_436;
goto block_418;
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_436, 0);
lean_inc(x_439);
lean_dec(x_436);
x_440 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_440, 0, x_439);
x_358 = x_419;
x_359 = x_432;
x_360 = x_433;
x_361 = x_428;
x_362 = x_431;
x_363 = x_429;
x_364 = x_426;
x_365 = x_430;
x_366 = x_425;
x_367 = x_427;
x_368 = x_421;
x_369 = x_422;
x_370 = x_424;
x_371 = x_423;
x_372 = x_440;
goto block_418;
}
}
}
block_471:
{
lean_object* x_458; uint8_t x_459; 
x_458 = l_Lean_Syntax_getArg(x_446, x_444);
x_459 = l_Lean_Syntax_isNone(x_458);
if (x_459 == 0)
{
uint8_t x_460; 
lean_inc(x_458);
x_460 = l_Lean_Syntax_matchesNull(x_458, x_442);
if (x_460 == 0)
{
lean_object* x_461; 
lean_dec(x_458);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_461 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_457);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; 
x_462 = l_Lean_Syntax_getArg(x_458, x_69);
lean_dec(x_458);
x_463 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_464 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_463);
lean_inc(x_462);
x_465 = l_Lean_Syntax_isOfKind(x_462, x_464);
lean_dec(x_464);
if (x_465 == 0)
{
lean_object* x_466; 
lean_dec(x_462);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_466 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_457);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = l_Lean_Syntax_getArg(x_462, x_442);
lean_dec(x_462);
x_468 = l_Lean_Syntax_getArgs(x_467);
lean_dec(x_467);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_468);
x_419 = x_443;
x_420 = x_446;
x_421 = x_445;
x_422 = x_448;
x_423 = x_447;
x_424 = x_469;
x_425 = x_449;
x_426 = x_450;
x_427 = x_451;
x_428 = x_452;
x_429 = x_453;
x_430 = x_454;
x_431 = x_455;
x_432 = x_456;
x_433 = x_457;
goto block_441;
}
}
}
else
{
lean_object* x_470; 
lean_dec(x_458);
x_470 = lean_box(0);
x_419 = x_443;
x_420 = x_446;
x_421 = x_445;
x_422 = x_448;
x_423 = x_447;
x_424 = x_470;
x_425 = x_449;
x_426 = x_450;
x_427 = x_451;
x_428 = x_452;
x_429 = x_453;
x_430 = x_454;
x_431 = x_455;
x_432 = x_456;
x_433 = x_457;
goto block_441;
}
}
block_500:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_482 = lean_unsigned_to_nat(2u);
x_483 = l_Lean_Syntax_getArg(x_6, x_482);
x_484 = lean_mk_string_unchecked("dsimpTraceArgsRest", 18, 18);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_485 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_484);
lean_inc(x_483);
x_486 = l_Lean_Syntax_isOfKind(x_483, x_485);
lean_dec(x_485);
if (x_486 == 0)
{
lean_object* x_487; 
lean_dec(x_483);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_487 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_481);
return x_487;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
x_488 = l_Lean_Syntax_getArg(x_483, x_69);
x_489 = lean_mk_string_unchecked("optConfig", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_490 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_489);
lean_inc(x_488);
x_491 = l_Lean_Syntax_isOfKind(x_488, x_490);
lean_dec(x_490);
if (x_491 == 0)
{
lean_object* x_492; 
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_492 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_481);
return x_492;
}
else
{
lean_object* x_493; uint8_t x_494; 
x_493 = l_Lean_Syntax_getArg(x_483, x_442);
x_494 = l_Lean_Syntax_isNone(x_493);
if (x_494 == 0)
{
uint8_t x_495; 
lean_inc(x_493);
x_495 = l_Lean_Syntax_matchesNull(x_493, x_442);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_493);
lean_dec(x_488);
lean_dec(x_483);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_496 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_481);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; 
x_497 = l_Lean_Syntax_getArg(x_493, x_69);
lean_dec(x_493);
x_498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_498, 0, x_497);
x_443 = x_491;
x_444 = x_482;
x_445 = x_488;
x_446 = x_483;
x_447 = x_472;
x_448 = x_498;
x_449 = x_473;
x_450 = x_474;
x_451 = x_475;
x_452 = x_476;
x_453 = x_477;
x_454 = x_478;
x_455 = x_479;
x_456 = x_480;
x_457 = x_481;
goto block_471;
}
}
else
{
lean_object* x_499; 
lean_dec(x_493);
x_499 = lean_box(0);
x_443 = x_491;
x_444 = x_482;
x_445 = x_488;
x_446 = x_483;
x_447 = x_472;
x_448 = x_499;
x_449 = x_473;
x_450 = x_474;
x_451 = x_475;
x_452 = x_476;
x_453 = x_477;
x_454 = x_478;
x_455 = x_479;
x_456 = x_480;
x_457 = x_481;
goto block_471;
}
}
}
}
}
block_67:
{
lean_object* x_30; 
lean_inc(x_24);
lean_inc(x_25);
lean_inc(x_27);
x_30 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_28, x_19, x_29, x_17, x_20, x_16, x_18, x_23, x_27, x_25, x_24, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_inc(x_24);
lean_inc(x_25);
lean_inc(x_27);
lean_inc(x_23);
x_34 = l_Lean_Elab_Tactic_mkSimpCallStx(x_21, x_33, x_23, x_27, x_25, x_24, x_32);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_25, 5);
lean_inc(x_37);
x_38 = lean_mk_string_unchecked("tactic", 6, 6);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = lean_box(0);
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set(x_45, 5, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_37);
x_47 = lean_mk_string_unchecked("Try this: ", 10, 10);
x_48 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_22, x_45, x_46, x_47, x_41, x_23, x_27, x_25, x_24, x_36);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_46);
lean_dec(x_22);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_dec(x_31);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_dec(x_31);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_31);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_59 = !lean_is_exclusive(x_34);
if (x_59 == 0)
{
return x_34;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_34, 0);
x_61 = lean_ctor_get(x_34, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_34);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_63 = !lean_is_exclusive(x_30);
if (x_63 == 0)
{
return x_30;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_30, 0);
x_65 = lean_ctor_get(x_30, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_30);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Parser", 6, 6);
x_13 = lean_mk_string_unchecked("Tactic", 6, 6);
x_14 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(1);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_11);
lean_closure_set(x_19, 3, x_12);
lean_closure_set(x_19, 4, x_13);
lean_closure_set(x_19, 5, x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = l_Lean_Elab_Tactic_withMainContext___redArg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalDSimpTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalDSimpTrace", 14, 14);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("evalDSimpTrace", 14, 14);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(82u);
x_8 = lean_unsigned_to_nat(29u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(95u);
x_11 = lean_unsigned_to_nat(31u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(33u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(47u);
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
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ElabRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
