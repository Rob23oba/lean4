// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp
// Imports: Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.Renaming Lean.Compiler.LCNF.Simp.Basic Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.JpCases Lean.Compiler.LCNF.Simp.Config Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.SimpM Lean.Compiler.LCNF.Simp.Main Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.Used
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
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_712_(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_100; 
x_100 = lean_ctor_get(x_1, 4);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
x_104 = lean_unbox(x_103);
lean_inc(x_101);
x_105 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_101, x_104, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_202; lean_object* x_203; lean_object* x_330; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_mk_string_unchecked("Compiler", 8, 8);
x_108 = lean_mk_string_unchecked("simp", 4, 4);
x_349 = lean_mk_string_unchecked("inline", 6, 6);
x_350 = lean_mk_string_unchecked("info", 4, 4);
lean_inc(x_108);
lean_inc(x_107);
x_351 = l_Lean_Name_mkStr4(x_107, x_108, x_349, x_350);
lean_inc(x_351);
x_352 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_351, x_7, x_106);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_unbox(x_353);
lean_dec(x_353);
if (x_354 == 0)
{
lean_object* x_355; 
lean_dec(x_351);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
lean_dec(x_352);
x_330 = x_355;
goto block_348;
}
else
{
uint8_t x_356; 
x_356 = !lean_is_exclusive(x_352);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_357 = lean_ctor_get(x_352, 1);
x_358 = lean_ctor_get(x_352, 0);
lean_dec(x_358);
x_359 = lean_st_ref_get(x_3, x_357);
x_360 = !lean_is_exclusive(x_359);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_359, 0);
x_362 = lean_ctor_get(x_359, 1);
x_363 = lean_ctor_get(x_361, 3);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_363, x_5, x_6, x_7, x_8, x_362);
lean_dec(x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = lean_mk_string_unchecked("", 0, 0);
x_368 = l_Lean_stringToMessageData(x_367);
lean_dec(x_367);
x_369 = lean_ctor_get(x_1, 0);
lean_inc(x_369);
x_370 = l_Lean_MessageData_ofName(x_369);
lean_inc(x_368);
lean_ctor_set_tag(x_359, 7);
lean_ctor_set(x_359, 1, x_370);
lean_ctor_set(x_359, 0, x_368);
x_371 = lean_mk_string_unchecked(":", 1, 1);
x_372 = l_Lean_stringToMessageData(x_371);
lean_dec(x_371);
lean_ctor_set_tag(x_352, 7);
lean_ctor_set(x_352, 1, x_372);
lean_ctor_set(x_352, 0, x_359);
x_373 = lean_unsigned_to_nat(2u);
x_374 = lean_nat_to_int(x_373);
x_375 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_365);
x_376 = l_Lean_MessageData_ofFormat(x_375);
x_377 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_377, 0, x_352);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_368);
x_379 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_351, x_378, x_6, x_7, x_8, x_366);
x_380 = lean_ctor_get(x_379, 1);
lean_inc(x_380);
lean_dec(x_379);
x_330 = x_380;
goto block_348;
}
else
{
uint8_t x_381; 
lean_free_object(x_359);
lean_free_object(x_352);
lean_dec(x_351);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_364);
if (x_381 == 0)
{
return x_364;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_364, 0);
x_383 = lean_ctor_get(x_364, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_364);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_385 = lean_ctor_get(x_359, 0);
x_386 = lean_ctor_get(x_359, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_359);
x_387 = lean_ctor_get(x_385, 3);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_387, x_5, x_6, x_7, x_8, x_386);
lean_dec(x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_mk_string_unchecked("", 0, 0);
x_392 = l_Lean_stringToMessageData(x_391);
lean_dec(x_391);
x_393 = lean_ctor_get(x_1, 0);
lean_inc(x_393);
x_394 = l_Lean_MessageData_ofName(x_393);
lean_inc(x_392);
x_395 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_394);
x_396 = lean_mk_string_unchecked(":", 1, 1);
x_397 = l_Lean_stringToMessageData(x_396);
lean_dec(x_396);
lean_ctor_set_tag(x_352, 7);
lean_ctor_set(x_352, 1, x_397);
lean_ctor_set(x_352, 0, x_395);
x_398 = lean_unsigned_to_nat(2u);
x_399 = lean_nat_to_int(x_398);
x_400 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_389);
x_401 = l_Lean_MessageData_ofFormat(x_400);
x_402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_402, 0, x_352);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_392);
x_404 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_351, x_403, x_6, x_7, x_8, x_390);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_330 = x_405;
goto block_348;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_free_object(x_352);
lean_dec(x_351);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_406 = lean_ctor_get(x_388, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_388, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_408 = x_388;
} else {
 lean_dec_ref(x_388);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_410 = lean_ctor_get(x_352, 1);
lean_inc(x_410);
lean_dec(x_352);
x_411 = lean_st_ref_get(x_3, x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_414 = x_411;
} else {
 lean_dec_ref(x_411);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_412, 3);
lean_inc(x_415);
lean_dec(x_412);
x_416 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_415, x_5, x_6, x_7, x_8, x_413);
lean_dec(x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = lean_mk_string_unchecked("", 0, 0);
x_420 = l_Lean_stringToMessageData(x_419);
lean_dec(x_419);
x_421 = lean_ctor_get(x_1, 0);
lean_inc(x_421);
x_422 = l_Lean_MessageData_ofName(x_421);
lean_inc(x_420);
if (lean_is_scalar(x_414)) {
 x_423 = lean_alloc_ctor(7, 2, 0);
} else {
 x_423 = x_414;
 lean_ctor_set_tag(x_423, 7);
}
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_422);
x_424 = lean_mk_string_unchecked(":", 1, 1);
x_425 = l_Lean_stringToMessageData(x_424);
lean_dec(x_424);
x_426 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_425);
x_427 = lean_unsigned_to_nat(2u);
x_428 = lean_nat_to_int(x_427);
x_429 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_417);
x_430 = l_Lean_MessageData_ofFormat(x_429);
x_431 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_431, 0, x_426);
lean_ctor_set(x_431, 1, x_430);
x_432 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_420);
x_433 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_351, x_432, x_6, x_7, x_8, x_418);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
lean_dec(x_433);
x_330 = x_434;
goto block_348;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_414);
lean_dec(x_351);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_435 = lean_ctor_get(x_416, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_416, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_437 = x_416;
} else {
 lean_dec_ref(x_416);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
}
block_201:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_mk_string_unchecked("stat", 4, 4);
x_113 = l_Lean_Name_mkStr3(x_107, x_108, x_112);
lean_inc(x_113);
x_114 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_113, x_7, x_111);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_113);
lean_dec(x_109);
lean_dec(x_102);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_10 = x_110;
x_11 = x_3;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_117;
goto block_99;
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_114);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_119 = lean_ctor_get(x_114, 1);
x_120 = lean_ctor_get(x_114, 0);
lean_dec(x_120);
x_121 = lean_mk_string_unchecked("", 0, 0);
x_122 = l_Lean_stringToMessageData(x_121);
lean_dec(x_121);
x_123 = lean_ctor_get(x_1, 0);
lean_inc(x_123);
x_124 = l_Lean_MessageData_ofName(x_123);
lean_inc(x_122);
lean_ctor_set_tag(x_114, 7);
lean_ctor_set(x_114, 1, x_124);
lean_ctor_set(x_114, 0, x_122);
x_125 = lean_mk_string_unchecked(", size: ", 8, 8);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_114);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Compiler_LCNF_Code_size(x_110);
x_129 = l___private_Init_Data_Repr_0__Nat_reprFast(x_128);
if (lean_is_scalar(x_102)) {
 x_130 = lean_alloc_ctor(3, 1, 0);
} else {
 x_130 = x_102;
 lean_ctor_set_tag(x_130, 3);
}
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Lean_MessageData_ofFormat(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_mk_string_unchecked(", # visited: ", 13, 13);
x_134 = l_Lean_stringToMessageData(x_133);
lean_dec(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_ctor_get(x_109, 4);
lean_inc(x_136);
x_137 = l___private_Init_Data_Repr_0__Nat_reprFast(x_136);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_mk_string_unchecked(", # inline: ", 12, 12);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_ctor_get(x_109, 5);
lean_inc(x_144);
x_145 = l___private_Init_Data_Repr_0__Nat_reprFast(x_144);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_MessageData_ofFormat(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_mk_string_unchecked(", # inline local: ", 18, 18);
x_150 = l_Lean_stringToMessageData(x_149);
lean_dec(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_ctor_get(x_109, 6);
lean_inc(x_152);
lean_dec(x_109);
x_153 = l___private_Init_Data_Repr_0__Nat_reprFast(x_152);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = l_Lean_MessageData_ofFormat(x_154);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_122);
x_158 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_113, x_157, x_6, x_7, x_8, x_119);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_10 = x_110;
x_11 = x_3;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_159;
goto block_99;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_160 = lean_ctor_get(x_114, 1);
lean_inc(x_160);
lean_dec(x_114);
x_161 = lean_mk_string_unchecked("", 0, 0);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
x_164 = l_Lean_MessageData_ofName(x_163);
lean_inc(x_162);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_mk_string_unchecked(", size: ", 8, 8);
x_167 = l_Lean_stringToMessageData(x_166);
lean_dec(x_166);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_Compiler_LCNF_Code_size(x_110);
x_170 = l___private_Init_Data_Repr_0__Nat_reprFast(x_169);
if (lean_is_scalar(x_102)) {
 x_171 = lean_alloc_ctor(3, 1, 0);
} else {
 x_171 = x_102;
 lean_ctor_set_tag(x_171, 3);
}
lean_ctor_set(x_171, 0, x_170);
x_172 = l_Lean_MessageData_ofFormat(x_171);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_mk_string_unchecked(", # visited: ", 13, 13);
x_175 = l_Lean_stringToMessageData(x_174);
lean_dec(x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_ctor_get(x_109, 4);
lean_inc(x_177);
x_178 = l___private_Init_Data_Repr_0__Nat_reprFast(x_177);
x_179 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = l_Lean_MessageData_ofFormat(x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_mk_string_unchecked(", # inline: ", 12, 12);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_ctor_get(x_109, 5);
lean_inc(x_185);
x_186 = l___private_Init_Data_Repr_0__Nat_reprFast(x_185);
x_187 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_188 = l_Lean_MessageData_ofFormat(x_187);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_184);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_mk_string_unchecked(", # inline local: ", 18, 18);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_ctor_get(x_109, 6);
lean_inc(x_193);
lean_dec(x_109);
x_194 = l___private_Init_Data_Repr_0__Nat_reprFast(x_193);
x_195 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = l_Lean_MessageData_ofFormat(x_195);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_162);
x_199 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_113, x_198, x_6, x_7, x_8, x_160);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_10 = x_110;
x_11 = x_3;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_200;
goto block_99;
}
}
}
block_329:
{
lean_object* x_204; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_204 = l_Lean_Compiler_LCNF_Simp_simp(x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_st_ref_get(x_3, x_206);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ctor_get(x_207, 1);
x_211 = lean_ctor_get(x_209, 2);
lean_inc(x_211);
x_212 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_205, x_211, x_5, x_6, x_7, x_8, x_210);
lean_dec(x_211);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_ctor_get(x_212, 1);
x_216 = lean_mk_string_unchecked("new", 3, 3);
lean_inc(x_108);
lean_inc(x_107);
x_217 = l_Lean_Name_mkStr4(x_107, x_108, x_202, x_216);
lean_inc(x_217);
x_218 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_217, x_7, x_215);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_unbox(x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_217);
lean_free_object(x_212);
lean_free_object(x_207);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_109 = x_209;
x_110 = x_214;
x_111 = x_221;
goto block_201;
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_218);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_218, 1);
x_224 = lean_ctor_get(x_218, 0);
lean_dec(x_224);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_214);
x_225 = l_Lean_Compiler_LCNF_ppCode(x_214, x_5, x_6, x_7, x_8, x_223);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_mk_string_unchecked("", 0, 0);
x_229 = l_Lean_stringToMessageData(x_228);
lean_dec(x_228);
x_230 = lean_ctor_get(x_1, 0);
lean_inc(x_230);
x_231 = l_Lean_MessageData_ofName(x_230);
lean_inc(x_229);
lean_ctor_set_tag(x_218, 7);
lean_ctor_set(x_218, 1, x_231);
lean_ctor_set(x_218, 0, x_229);
x_232 = lean_mk_string_unchecked(" :=\n", 4, 4);
x_233 = l_Lean_stringToMessageData(x_232);
lean_dec(x_232);
lean_ctor_set_tag(x_212, 7);
lean_ctor_set(x_212, 1, x_233);
lean_ctor_set(x_212, 0, x_218);
x_234 = l_Lean_MessageData_ofFormat(x_226);
lean_ctor_set_tag(x_207, 7);
lean_ctor_set(x_207, 1, x_234);
lean_ctor_set(x_207, 0, x_212);
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_207);
lean_ctor_set(x_235, 1, x_229);
x_236 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_217, x_235, x_6, x_7, x_8, x_227);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_109 = x_209;
x_110 = x_214;
x_111 = x_237;
goto block_201;
}
else
{
uint8_t x_238; 
lean_free_object(x_218);
lean_dec(x_217);
lean_free_object(x_212);
lean_dec(x_214);
lean_free_object(x_207);
lean_dec(x_209);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_225);
if (x_238 == 0)
{
return x_225;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_225, 0);
x_240 = lean_ctor_get(x_225, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_225);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_218, 1);
lean_inc(x_242);
lean_dec(x_218);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_214);
x_243 = l_Lean_Compiler_LCNF_ppCode(x_214, x_5, x_6, x_7, x_8, x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_mk_string_unchecked("", 0, 0);
x_247 = l_Lean_stringToMessageData(x_246);
lean_dec(x_246);
x_248 = lean_ctor_get(x_1, 0);
lean_inc(x_248);
x_249 = l_Lean_MessageData_ofName(x_248);
lean_inc(x_247);
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_mk_string_unchecked(" :=\n", 4, 4);
x_252 = l_Lean_stringToMessageData(x_251);
lean_dec(x_251);
lean_ctor_set_tag(x_212, 7);
lean_ctor_set(x_212, 1, x_252);
lean_ctor_set(x_212, 0, x_250);
x_253 = l_Lean_MessageData_ofFormat(x_244);
lean_ctor_set_tag(x_207, 7);
lean_ctor_set(x_207, 1, x_253);
lean_ctor_set(x_207, 0, x_212);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_207);
lean_ctor_set(x_254, 1, x_247);
x_255 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_217, x_254, x_6, x_7, x_8, x_245);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_109 = x_209;
x_110 = x_214;
x_111 = x_256;
goto block_201;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_217);
lean_free_object(x_212);
lean_dec(x_214);
lean_free_object(x_207);
lean_dec(x_209);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_257 = lean_ctor_get(x_243, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_243, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_259 = x_243;
} else {
 lean_dec_ref(x_243);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_261 = lean_ctor_get(x_212, 0);
x_262 = lean_ctor_get(x_212, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_212);
x_263 = lean_mk_string_unchecked("new", 3, 3);
lean_inc(x_108);
lean_inc(x_107);
x_264 = l_Lean_Name_mkStr4(x_107, x_108, x_202, x_263);
lean_inc(x_264);
x_265 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_264, x_7, x_262);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_unbox(x_266);
lean_dec(x_266);
if (x_267 == 0)
{
lean_object* x_268; 
lean_dec(x_264);
lean_free_object(x_207);
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_268);
lean_dec(x_265);
x_109 = x_209;
x_110 = x_261;
x_111 = x_268;
goto block_201;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_265, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_270 = x_265;
} else {
 lean_dec_ref(x_265);
 x_270 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_261);
x_271 = l_Lean_Compiler_LCNF_ppCode(x_261, x_5, x_6, x_7, x_8, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_mk_string_unchecked("", 0, 0);
x_275 = l_Lean_stringToMessageData(x_274);
lean_dec(x_274);
x_276 = lean_ctor_get(x_1, 0);
lean_inc(x_276);
x_277 = l_Lean_MessageData_ofName(x_276);
lean_inc(x_275);
if (lean_is_scalar(x_270)) {
 x_278 = lean_alloc_ctor(7, 2, 0);
} else {
 x_278 = x_270;
 lean_ctor_set_tag(x_278, 7);
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_mk_string_unchecked(" :=\n", 4, 4);
x_280 = l_Lean_stringToMessageData(x_279);
lean_dec(x_279);
x_281 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_280);
x_282 = l_Lean_MessageData_ofFormat(x_272);
lean_ctor_set_tag(x_207, 7);
lean_ctor_set(x_207, 1, x_282);
lean_ctor_set(x_207, 0, x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_207);
lean_ctor_set(x_283, 1, x_275);
x_284 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_264, x_283, x_6, x_7, x_8, x_273);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
lean_dec(x_284);
x_109 = x_209;
x_110 = x_261;
x_111 = x_285;
goto block_201;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_261);
lean_free_object(x_207);
lean_dec(x_209);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_286 = lean_ctor_get(x_271, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_271, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_288 = x_271;
} else {
 lean_dec_ref(x_271);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_290 = lean_ctor_get(x_207, 0);
x_291 = lean_ctor_get(x_207, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_207);
x_292 = lean_ctor_get(x_290, 2);
lean_inc(x_292);
x_293 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_205, x_292, x_5, x_6, x_7, x_8, x_291);
lean_dec(x_292);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
x_297 = lean_mk_string_unchecked("new", 3, 3);
lean_inc(x_108);
lean_inc(x_107);
x_298 = l_Lean_Name_mkStr4(x_107, x_108, x_202, x_297);
lean_inc(x_298);
x_299 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_298, x_7, x_295);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_unbox(x_300);
lean_dec(x_300);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_298);
lean_dec(x_296);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_109 = x_290;
x_110 = x_294;
x_111 = x_302;
goto block_201;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_299, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_304 = x_299;
} else {
 lean_dec_ref(x_299);
 x_304 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_294);
x_305 = l_Lean_Compiler_LCNF_ppCode(x_294, x_5, x_6, x_7, x_8, x_303);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_mk_string_unchecked("", 0, 0);
x_309 = l_Lean_stringToMessageData(x_308);
lean_dec(x_308);
x_310 = lean_ctor_get(x_1, 0);
lean_inc(x_310);
x_311 = l_Lean_MessageData_ofName(x_310);
lean_inc(x_309);
if (lean_is_scalar(x_304)) {
 x_312 = lean_alloc_ctor(7, 2, 0);
} else {
 x_312 = x_304;
 lean_ctor_set_tag(x_312, 7);
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_mk_string_unchecked(" :=\n", 4, 4);
x_314 = l_Lean_stringToMessageData(x_313);
lean_dec(x_313);
if (lean_is_scalar(x_296)) {
 x_315 = lean_alloc_ctor(7, 2, 0);
} else {
 x_315 = x_296;
 lean_ctor_set_tag(x_315, 7);
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_MessageData_ofFormat(x_306);
x_317 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_309);
x_319 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_298, x_318, x_6, x_7, x_8, x_307);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_109 = x_290;
x_110 = x_294;
x_111 = x_320;
goto block_201;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_304);
lean_dec(x_298);
lean_dec(x_296);
lean_dec(x_294);
lean_dec(x_290);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_321 = lean_ctor_get(x_305, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_305, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_323 = x_305;
} else {
 lean_dec_ref(x_305);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_202);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_204);
if (x_325 == 0)
{
return x_204;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_204, 0);
x_327 = lean_ctor_get(x_204, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_204);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
block_348:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_mk_string_unchecked("step", 4, 4);
lean_inc(x_331);
lean_inc(x_108);
lean_inc(x_107);
x_332 = l_Lean_Name_mkStr3(x_107, x_108, x_331);
lean_inc(x_332);
x_333 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_332, x_7, x_330);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_unbox(x_334);
lean_dec(x_334);
if (x_335 == 0)
{
lean_object* x_336; 
lean_dec(x_332);
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
lean_dec(x_333);
x_202 = x_331;
x_203 = x_336;
goto block_329;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_333, 1);
lean_inc(x_337);
lean_dec(x_333);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_338 = l_Lean_Compiler_LCNF_ppDecl(x_1, x_5, x_6, x_7, x_8, x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Lean_MessageData_ofFormat(x_339);
x_342 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_332, x_341, x_6, x_7, x_8, x_340);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_202 = x_331;
x_203 = x_343;
goto block_329;
}
else
{
uint8_t x_344; 
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_344 = !lean_is_exclusive(x_338);
if (x_344 == 0)
{
return x_338;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_338, 0);
x_346 = lean_ctor_get(x_338, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_338);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
}
}
else
{
uint8_t x_439; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_439 = !lean_is_exclusive(x_105);
if (x_439 == 0)
{
return x_105;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_105, 0);
x_441 = lean_ctor_get(x_105, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_105);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_100);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_443 = lean_box(0);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_9);
return x_444;
}
block_99:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
x_17 = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(x_10, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_11, x_19);
lean_dec(x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*7);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_10);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_38 = lean_ctor_get(x_1, 5);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_35);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 1, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_20, 0, x_40);
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec(x_20);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_10);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_49 = lean_ctor_get(x_1, 5);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_44);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*6, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*6 + 1, x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_11);
lean_dec(x_10);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_dec(x_17);
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_18, 0);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 3);
lean_inc(x_59);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_61 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_62 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_63 = lean_ctor_get(x_1, 5);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_64, 2, x_58);
lean_ctor_set(x_64, 3, x_59);
lean_ctor_set(x_64, 4, x_60);
lean_ctor_set(x_64, 5, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 1, x_62);
x_65 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_64, x_12, x_13, x_14, x_15, x_53);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_ctor_set(x_18, 0, x_67);
lean_ctor_set(x_65, 0, x_18);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
lean_ctor_set(x_18, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_free_object(x_18);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_18, 0);
lean_inc(x_75);
lean_dec(x_18);
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 3);
lean_inc(x_79);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_81 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_82 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_83 = lean_ctor_get(x_1, 5);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_79);
lean_ctor_set(x_84, 4, x_80);
lean_ctor_set(x_84, 5, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*6, x_81);
lean_ctor_set_uint8(x_84, sizeof(void*)*6 + 1, x_82);
x_85 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_84, x_12, x_13, x_14, x_15, x_53);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_86);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_93 = x_85;
} else {
 lean_dec_ref(x_85);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_17);
if (x_95 == 0)
{
return x_17;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_17, 0);
x_97 = lean_ctor_get(x_17, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_17);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_8 = lean_unsigned_to_nat(8u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_shiftl(x_8, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_nextPowerOfTwo(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_box(0);
lean_inc_n(x_17, 2);
x_20 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_9);
lean_ctor_set(x_20, 5, x_9);
lean_ctor_set(x_20, 6, x_9);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*7, x_21);
x_22 = lean_st_mk_ref(x_20, x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_box(0);
lean_inc(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_26);
lean_inc(x_2);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_22, 1, x_30);
lean_ctor_set(x_22, 0, x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_24);
lean_inc(x_1);
x_32 = l_Lean_Compiler_LCNF_Decl_simp_x3f(x_1, x_31, x_24, x_22, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_24, x_34);
lean_dec(x_24);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_1);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_1 = x_41;
x_7 = x_40;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_box(0);
lean_inc(x_49);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_49);
lean_inc(x_2);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_18);
lean_ctor_set(x_55, 1, x_53);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_47);
lean_inc(x_1);
x_56 = l_Lean_Compiler_LCNF_Decl_simp_x3f(x_1, x_54, x_47, x_55, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_47, x_58);
lean_dec(x_47);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
lean_dec(x_57);
x_1 = x_64;
x_7 = x_63;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_ctor_get(x_56, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_68 = x_56;
} else {
 lean_dec_ref(x_56);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(x_1, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_ctor_get_uint8(x_2, 2);
x_16 = lean_ctor_get_uint8(x_2, 3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 0, 4);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, 0, x_18);
x_19 = lean_unbox(x_14);
lean_ctor_set_uint8(x_17, 1, x_19);
lean_ctor_set_uint8(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, 3, x_16);
x_20 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_17, x_3, x_4, x_5, x_6, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Decl_simp(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__0), 7, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_mk_string_unchecked("simp", 4, 4);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_6, x_4, x_3, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_712_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("LCNF", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
lean_inc(x_2);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("Simp", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(712u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
lean_inc(x_24);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("stat", 4, 4);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Name_mkStr3(x_2, x_3, x_28);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_24);
x_32 = l_Lean_registerTraceClass(x_29, x_31, x_24, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("step", 4, 4);
lean_inc(x_34);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_Lean_Name_mkStr3(x_2, x_3, x_34);
x_36 = lean_unbox(x_30);
lean_inc(x_24);
x_37 = l_Lean_registerTraceClass(x_35, x_36, x_24, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_mk_string_unchecked("new", 3, 3);
x_40 = l_Lean_Name_mkStr4(x_2, x_3, x_34, x_39);
x_41 = lean_unbox(x_30);
x_42 = l_Lean_registerTraceClass(x_40, x_41, x_24, x_38);
return x_42;
}
else
{
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
}
else
{
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
}
else
{
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Renaming(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_712_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
