// Lean compiler output
// Module: Lean.Elab.Mixfix
// Imports: Lean.Elab.Attributes
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
extern lean_object* l_Lean_Elab_mkAttrKindGlobal;
lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__1(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMixfix__1(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix_withAttrKindGlobal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Elab_mkAttrKindGlobal;
lean_inc(x_1);
x_7 = l_Lean_Syntax_setArg(x_1, x_5, x_6);
x_8 = lean_apply_3(x_2, x_7, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_12 = l_Lean_Syntax_setArg(x_10, x_5, x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_16 = l_Lean_Syntax_setArg(x_13, x_5, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_850; uint8_t x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_1027; lean_object* x_1028; uint8_t x_1029; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Command", 7, 7);
x_1027 = lean_mk_string_unchecked("mixfix", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1028 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1027);
lean_inc(x_1);
x_1029 = l_Lean_Syntax_isOfKind(x_1, x_1028);
lean_dec(x_1028);
if (x_1029 == 0)
{
lean_object* x_1030; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1030 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_1030;
}
else
{
lean_object* x_1031; uint8_t x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; uint8_t x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1314; uint8_t x_1315; 
x_1031 = lean_unsigned_to_nat(0u);
x_1314 = l_Lean_Syntax_getArg(x_1, x_1031);
x_1315 = l_Lean_Syntax_isNone(x_1314);
if (x_1315 == 0)
{
lean_object* x_1316; uint8_t x_1317; 
x_1316 = lean_unsigned_to_nat(1u);
lean_inc(x_1314);
x_1317 = l_Lean_Syntax_matchesNull(x_1314, x_1316);
if (x_1317 == 0)
{
lean_object* x_1318; 
lean_dec(x_1314);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1318 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_1318;
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; uint8_t x_1322; 
x_1319 = l_Lean_Syntax_getArg(x_1314, x_1031);
lean_dec(x_1314);
x_1320 = lean_mk_string_unchecked("docComment", 10, 10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1321 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1320);
lean_inc(x_1319);
x_1322 = l_Lean_Syntax_isOfKind(x_1319, x_1321);
lean_dec(x_1321);
if (x_1322 == 0)
{
lean_object* x_1323; 
lean_dec(x_1319);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1323 = l_Lean_Macro_throwUnsupported(lean_box(0), x_2, x_3);
lean_dec(x_2);
return x_1323;
}
else
{
lean_object* x_1324; 
x_1324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1324, 0, x_1319);
x_1295 = x_1324;
x_1296 = x_2;
x_1297 = x_3;
goto block_1313;
}
}
}
else
{
lean_object* x_1325; 
lean_dec(x_1314);
x_1325 = lean_box(0);
x_1295 = x_1325;
x_1296 = x_2;
x_1297 = x_3;
goto block_1313;
}
block_1057:
{
lean_object* x_1044; lean_object* x_1045; uint8_t x_1046; 
x_1044 = lean_unsigned_to_nat(6u);
x_1045 = l_Lean_Syntax_getArg(x_1, x_1044);
x_1046 = l_Lean_Syntax_isNone(x_1045);
if (x_1046 == 0)
{
uint8_t x_1047; 
lean_inc(x_1045);
x_1047 = l_Lean_Syntax_matchesNull(x_1045, x_1038);
if (x_1047 == 0)
{
lean_object* x_1048; 
lean_dec(x_1045);
lean_dec(x_1041);
lean_dec(x_1040);
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1048 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1042, x_1043);
lean_dec(x_1042);
return x_1048;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; 
x_1049 = l_Lean_Syntax_getArg(x_1045, x_1031);
lean_dec(x_1045);
x_1050 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1051 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1050);
lean_inc(x_1049);
x_1052 = l_Lean_Syntax_isOfKind(x_1049, x_1051);
lean_dec(x_1051);
if (x_1052 == 0)
{
lean_object* x_1053; 
lean_dec(x_1049);
lean_dec(x_1041);
lean_dec(x_1040);
lean_dec(x_1039);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_1035);
lean_dec(x_1033);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1053 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1042, x_1043);
lean_dec(x_1042);
return x_1053;
}
else
{
lean_object* x_1054; lean_object* x_1055; 
x_1054 = l_Lean_Syntax_getArg(x_1049, x_1034);
lean_dec(x_1049);
x_1055 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1055, 0, x_1054);
x_850 = x_1033;
x_851 = x_1032;
x_852 = x_1035;
x_853 = x_1036;
x_854 = x_1037;
x_855 = x_1039;
x_856 = x_1041;
x_857 = x_1040;
x_858 = x_1055;
x_859 = x_1042;
x_860 = x_1043;
goto block_877;
}
}
}
else
{
lean_object* x_1056; 
lean_dec(x_1045);
x_1056 = lean_box(0);
x_850 = x_1033;
x_851 = x_1032;
x_852 = x_1035;
x_853 = x_1036;
x_854 = x_1037;
x_855 = x_1039;
x_856 = x_1041;
x_857 = x_1040;
x_858 = x_1056;
x_859 = x_1042;
x_860 = x_1043;
goto block_877;
}
}
block_1083:
{
lean_object* x_1070; lean_object* x_1071; uint8_t x_1072; 
x_1070 = lean_unsigned_to_nat(6u);
x_1071 = l_Lean_Syntax_getArg(x_1, x_1070);
x_1072 = l_Lean_Syntax_isNone(x_1071);
if (x_1072 == 0)
{
uint8_t x_1073; 
lean_inc(x_1071);
x_1073 = l_Lean_Syntax_matchesNull(x_1071, x_1065);
if (x_1073 == 0)
{
lean_object* x_1074; 
lean_dec(x_1071);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_1063);
lean_dec(x_1062);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1058);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1074 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1068, x_1069);
lean_dec(x_1068);
return x_1074;
}
else
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; uint8_t x_1078; 
x_1075 = l_Lean_Syntax_getArg(x_1071, x_1031);
lean_dec(x_1071);
x_1076 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1077 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1076);
lean_inc(x_1075);
x_1078 = l_Lean_Syntax_isOfKind(x_1075, x_1077);
lean_dec(x_1077);
if (x_1078 == 0)
{
lean_object* x_1079; 
lean_dec(x_1075);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_1063);
lean_dec(x_1062);
lean_dec(x_1061);
lean_dec(x_1060);
lean_dec(x_1058);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1079 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1068, x_1069);
lean_dec(x_1068);
return x_1079;
}
else
{
lean_object* x_1080; lean_object* x_1081; 
x_1080 = l_Lean_Syntax_getArg(x_1075, x_1059);
lean_dec(x_1075);
x_1081 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1081, 0, x_1080);
x_878 = x_1067;
x_879 = x_1058;
x_880 = x_1061;
x_881 = x_1060;
x_882 = x_1062;
x_883 = x_1063;
x_884 = x_1064;
x_885 = x_1066;
x_886 = x_1081;
x_887 = x_1068;
x_888 = x_1069;
goto block_905;
}
}
}
else
{
lean_object* x_1082; 
lean_dec(x_1071);
x_1082 = lean_box(0);
x_878 = x_1067;
x_879 = x_1058;
x_880 = x_1061;
x_881 = x_1060;
x_882 = x_1062;
x_883 = x_1063;
x_884 = x_1064;
x_885 = x_1066;
x_886 = x_1082;
x_887 = x_1068;
x_888 = x_1069;
goto block_905;
}
}
block_1109:
{
lean_object* x_1096; lean_object* x_1097; uint8_t x_1098; 
x_1096 = lean_unsigned_to_nat(6u);
x_1097 = l_Lean_Syntax_getArg(x_1, x_1096);
x_1098 = l_Lean_Syntax_isNone(x_1097);
if (x_1098 == 0)
{
uint8_t x_1099; 
lean_inc(x_1097);
x_1099 = l_Lean_Syntax_matchesNull(x_1097, x_1090);
if (x_1099 == 0)
{
lean_object* x_1100; 
lean_dec(x_1097);
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_1091);
lean_dec(x_1088);
lean_dec(x_1087);
lean_dec(x_1085);
lean_dec(x_1084);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1100 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1094, x_1095);
lean_dec(x_1094);
return x_1100;
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; uint8_t x_1104; 
x_1101 = l_Lean_Syntax_getArg(x_1097, x_1031);
lean_dec(x_1097);
x_1102 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1103 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1102);
lean_inc(x_1101);
x_1104 = l_Lean_Syntax_isOfKind(x_1101, x_1103);
lean_dec(x_1103);
if (x_1104 == 0)
{
lean_object* x_1105; 
lean_dec(x_1101);
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_1091);
lean_dec(x_1088);
lean_dec(x_1087);
lean_dec(x_1085);
lean_dec(x_1084);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1105 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1094, x_1095);
lean_dec(x_1094);
return x_1105;
}
else
{
lean_object* x_1106; lean_object* x_1107; 
x_1106 = l_Lean_Syntax_getArg(x_1101, x_1086);
lean_dec(x_1101);
x_1107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1107, 0, x_1106);
x_906 = x_1084;
x_907 = x_1085;
x_908 = x_1087;
x_909 = x_1088;
x_910 = x_1093;
x_911 = x_1089;
x_912 = x_1091;
x_913 = x_1090;
x_914 = x_1092;
x_915 = x_1107;
x_916 = x_1094;
x_917 = x_1095;
goto block_945;
}
}
}
else
{
lean_object* x_1108; 
lean_dec(x_1097);
x_1108 = lean_box(0);
x_906 = x_1084;
x_907 = x_1085;
x_908 = x_1087;
x_909 = x_1088;
x_910 = x_1093;
x_911 = x_1089;
x_912 = x_1091;
x_913 = x_1090;
x_914 = x_1092;
x_915 = x_1108;
x_916 = x_1094;
x_917 = x_1095;
goto block_945;
}
}
block_1135:
{
lean_object* x_1122; lean_object* x_1123; uint8_t x_1124; 
x_1122 = lean_unsigned_to_nat(6u);
x_1123 = l_Lean_Syntax_getArg(x_1, x_1122);
x_1124 = l_Lean_Syntax_isNone(x_1123);
if (x_1124 == 0)
{
uint8_t x_1125; 
lean_inc(x_1123);
x_1125 = l_Lean_Syntax_matchesNull(x_1123, x_1115);
if (x_1125 == 0)
{
lean_object* x_1126; 
lean_dec(x_1123);
lean_dec(x_1119);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1126 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1120, x_1121);
lean_dec(x_1120);
return x_1126;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; uint8_t x_1130; 
x_1127 = l_Lean_Syntax_getArg(x_1123, x_1031);
lean_dec(x_1123);
x_1128 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1129 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1128);
lean_inc(x_1127);
x_1130 = l_Lean_Syntax_isOfKind(x_1127, x_1129);
lean_dec(x_1129);
if (x_1130 == 0)
{
lean_object* x_1131; 
lean_dec(x_1127);
lean_dec(x_1119);
lean_dec(x_1117);
lean_dec(x_1116);
lean_dec(x_1114);
lean_dec(x_1113);
lean_dec(x_1112);
lean_dec(x_1110);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1131 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1120, x_1121);
lean_dec(x_1120);
return x_1131;
}
else
{
lean_object* x_1132; lean_object* x_1133; 
x_1132 = l_Lean_Syntax_getArg(x_1127, x_1111);
lean_dec(x_1127);
x_1133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1133, 0, x_1132);
x_946 = x_1110;
x_947 = x_1112;
x_948 = x_1119;
x_949 = x_1113;
x_950 = x_1114;
x_951 = x_1116;
x_952 = x_1115;
x_953 = x_1117;
x_954 = x_1118;
x_955 = x_1133;
x_956 = x_1120;
x_957 = x_1121;
goto block_985;
}
}
}
else
{
lean_object* x_1134; 
lean_dec(x_1123);
x_1134 = lean_box(0);
x_946 = x_1110;
x_947 = x_1112;
x_948 = x_1119;
x_949 = x_1113;
x_950 = x_1114;
x_951 = x_1116;
x_952 = x_1115;
x_953 = x_1117;
x_954 = x_1118;
x_955 = x_1134;
x_956 = x_1120;
x_957 = x_1121;
goto block_985;
}
}
block_1160:
{
lean_object* x_1147; lean_object* x_1148; uint8_t x_1149; 
x_1147 = lean_unsigned_to_nat(6u);
x_1148 = l_Lean_Syntax_getArg(x_1, x_1147);
x_1149 = l_Lean_Syntax_isNone(x_1148);
if (x_1149 == 0)
{
uint8_t x_1150; 
lean_inc(x_1148);
x_1150 = l_Lean_Syntax_matchesNull(x_1148, x_1141);
if (x_1150 == 0)
{
lean_object* x_1151; 
lean_dec(x_1148);
lean_dec(x_1144);
lean_dec(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1139);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1151 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1145, x_1146);
lean_dec(x_1145);
return x_1151;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; uint8_t x_1155; 
x_1152 = l_Lean_Syntax_getArg(x_1148, x_1031);
lean_dec(x_1148);
x_1153 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1154 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1153);
lean_inc(x_1152);
x_1155 = l_Lean_Syntax_isOfKind(x_1152, x_1154);
lean_dec(x_1154);
if (x_1155 == 0)
{
lean_object* x_1156; 
lean_dec(x_1152);
lean_dec(x_1144);
lean_dec(x_1143);
lean_dec(x_1142);
lean_dec(x_1140);
lean_dec(x_1139);
lean_dec(x_1138);
lean_dec(x_1136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1156 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1145, x_1146);
lean_dec(x_1145);
return x_1156;
}
else
{
lean_object* x_1157; lean_object* x_1158; 
x_1157 = l_Lean_Syntax_getArg(x_1152, x_1137);
lean_dec(x_1152);
x_1158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1158, 0, x_1157);
x_986 = x_1136;
x_987 = x_1138;
x_988 = x_1139;
x_989 = x_1140;
x_990 = x_1143;
x_991 = x_1142;
x_992 = x_1141;
x_993 = x_1144;
x_994 = x_1158;
x_995 = x_1145;
x_996 = x_1146;
goto block_1026;
}
}
}
else
{
lean_object* x_1159; 
lean_dec(x_1148);
x_1159 = lean_box(0);
x_986 = x_1136;
x_987 = x_1138;
x_988 = x_1139;
x_989 = x_1140;
x_990 = x_1143;
x_991 = x_1142;
x_992 = x_1141;
x_993 = x_1144;
x_994 = x_1159;
x_995 = x_1145;
x_996 = x_1146;
goto block_1026;
}
}
block_1294:
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; uint8_t x_1171; 
x_1166 = lean_unsigned_to_nat(2u);
x_1167 = l_Lean_Syntax_getArg(x_1, x_1166);
x_1168 = lean_mk_string_unchecked("Term", 4, 4);
x_1169 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_1168);
lean_inc(x_5);
lean_inc(x_4);
x_1170 = l_Lean_Name_mkStr4(x_4, x_5, x_1168, x_1169);
lean_inc(x_1167);
x_1171 = l_Lean_Syntax_isOfKind(x_1167, x_1170);
if (x_1171 == 0)
{
lean_object* x_1172; 
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1167);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1172 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1172;
}
else
{
lean_object* x_1173; uint8_t x_1174; 
x_1173 = l_Lean_Syntax_getArg(x_1167, x_1031);
lean_dec(x_1167);
x_1174 = l_Lean_Syntax_matchesNull(x_1173, x_1031);
if (x_1174 == 0)
{
lean_object* x_1175; 
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1175 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1175;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; 
x_1176 = lean_unsigned_to_nat(3u);
x_1177 = l_Lean_Syntax_getArg(x_1, x_1176);
x_1178 = lean_mk_string_unchecked("infixl", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1179 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1178);
lean_inc(x_1177);
x_1180 = l_Lean_Syntax_isOfKind(x_1177, x_1179);
lean_dec(x_1179);
if (x_1180 == 0)
{
lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; 
x_1181 = lean_mk_string_unchecked("infix", 5, 5);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1182 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1181);
lean_inc(x_1177);
x_1183 = l_Lean_Syntax_isOfKind(x_1177, x_1182);
lean_dec(x_1182);
if (x_1183 == 0)
{
lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; 
x_1184 = lean_mk_string_unchecked("infixr", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1185 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1184);
lean_inc(x_1177);
x_1186 = l_Lean_Syntax_isOfKind(x_1177, x_1185);
lean_dec(x_1185);
if (x_1186 == 0)
{
lean_object* x_1187; lean_object* x_1188; uint8_t x_1189; 
x_1187 = lean_mk_string_unchecked("prefix", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1188 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1187);
lean_inc(x_1177);
x_1189 = l_Lean_Syntax_isOfKind(x_1177, x_1188);
lean_dec(x_1188);
if (x_1189 == 0)
{
lean_object* x_1190; lean_object* x_1191; uint8_t x_1192; 
x_1190 = lean_mk_string_unchecked("postfix", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1191 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1190);
x_1192 = l_Lean_Syntax_isOfKind(x_1177, x_1191);
lean_dec(x_1191);
if (x_1192 == 0)
{
lean_object* x_1193; 
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1193 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1193;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; uint8_t x_1198; 
x_1194 = lean_unsigned_to_nat(4u);
x_1195 = l_Lean_Syntax_getArg(x_1, x_1194);
x_1196 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_5);
lean_inc(x_4);
x_1197 = l_Lean_Name_mkStr3(x_4, x_5, x_1196);
lean_inc(x_1195);
x_1198 = l_Lean_Syntax_isOfKind(x_1195, x_1197);
if (x_1198 == 0)
{
lean_object* x_1199; 
lean_dec(x_1197);
lean_dec(x_1195);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1199 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1199;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; uint8_t x_1203; 
x_1200 = l_Lean_Syntax_getArg(x_1195, x_1162);
lean_dec(x_1195);
x_1201 = lean_unsigned_to_nat(5u);
x_1202 = l_Lean_Syntax_getArg(x_1, x_1201);
x_1203 = l_Lean_Syntax_isNone(x_1202);
if (x_1203 == 0)
{
uint8_t x_1204; 
lean_inc(x_1202);
x_1204 = l_Lean_Syntax_matchesNull(x_1202, x_1162);
if (x_1204 == 0)
{
lean_object* x_1205; 
lean_dec(x_1202);
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1205 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1205;
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; uint8_t x_1209; 
x_1206 = l_Lean_Syntax_getArg(x_1202, x_1031);
lean_dec(x_1202);
x_1207 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1208 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1207);
lean_inc(x_1206);
x_1209 = l_Lean_Syntax_isOfKind(x_1206, x_1208);
lean_dec(x_1208);
if (x_1209 == 0)
{
lean_object* x_1210; 
lean_dec(x_1206);
lean_dec(x_1200);
lean_dec(x_1197);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1210 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1210;
}
else
{
lean_object* x_1211; lean_object* x_1212; 
x_1211 = l_Lean_Syntax_getArg(x_1206, x_1176);
lean_dec(x_1206);
x_1212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1212, 0, x_1211);
x_1032 = x_1189;
x_1033 = x_1161;
x_1034 = x_1176;
x_1035 = x_1168;
x_1036 = x_1197;
x_1037 = x_1170;
x_1038 = x_1162;
x_1039 = x_1163;
x_1040 = x_1200;
x_1041 = x_1212;
x_1042 = x_1164;
x_1043 = x_1165;
goto block_1057;
}
}
}
else
{
lean_object* x_1213; 
lean_dec(x_1202);
x_1213 = lean_box(0);
x_1032 = x_1189;
x_1033 = x_1161;
x_1034 = x_1176;
x_1035 = x_1168;
x_1036 = x_1197;
x_1037 = x_1170;
x_1038 = x_1162;
x_1039 = x_1163;
x_1040 = x_1200;
x_1041 = x_1213;
x_1042 = x_1164;
x_1043 = x_1165;
goto block_1057;
}
}
}
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; uint8_t x_1218; 
lean_dec(x_1177);
x_1214 = lean_unsigned_to_nat(4u);
x_1215 = l_Lean_Syntax_getArg(x_1, x_1214);
x_1216 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_5);
lean_inc(x_4);
x_1217 = l_Lean_Name_mkStr3(x_4, x_5, x_1216);
lean_inc(x_1215);
x_1218 = l_Lean_Syntax_isOfKind(x_1215, x_1217);
if (x_1218 == 0)
{
lean_object* x_1219; 
lean_dec(x_1217);
lean_dec(x_1215);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1219 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1219;
}
else
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; uint8_t x_1223; 
x_1220 = l_Lean_Syntax_getArg(x_1215, x_1162);
lean_dec(x_1215);
x_1221 = lean_unsigned_to_nat(5u);
x_1222 = l_Lean_Syntax_getArg(x_1, x_1221);
x_1223 = l_Lean_Syntax_isNone(x_1222);
if (x_1223 == 0)
{
uint8_t x_1224; 
lean_inc(x_1222);
x_1224 = l_Lean_Syntax_matchesNull(x_1222, x_1162);
if (x_1224 == 0)
{
lean_object* x_1225; 
lean_dec(x_1222);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1225 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1225;
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; uint8_t x_1229; 
x_1226 = l_Lean_Syntax_getArg(x_1222, x_1031);
lean_dec(x_1222);
x_1227 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1228 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1227);
lean_inc(x_1226);
x_1229 = l_Lean_Syntax_isOfKind(x_1226, x_1228);
lean_dec(x_1228);
if (x_1229 == 0)
{
lean_object* x_1230; 
lean_dec(x_1226);
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1230 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1230;
}
else
{
lean_object* x_1231; lean_object* x_1232; 
x_1231 = l_Lean_Syntax_getArg(x_1226, x_1176);
lean_dec(x_1226);
x_1232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1232, 0, x_1231);
x_1058 = x_1161;
x_1059 = x_1176;
x_1060 = x_1168;
x_1061 = x_1217;
x_1062 = x_1220;
x_1063 = x_1170;
x_1064 = x_1186;
x_1065 = x_1162;
x_1066 = x_1163;
x_1067 = x_1232;
x_1068 = x_1164;
x_1069 = x_1165;
goto block_1083;
}
}
}
else
{
lean_object* x_1233; 
lean_dec(x_1222);
x_1233 = lean_box(0);
x_1058 = x_1161;
x_1059 = x_1176;
x_1060 = x_1168;
x_1061 = x_1217;
x_1062 = x_1220;
x_1063 = x_1170;
x_1064 = x_1186;
x_1065 = x_1162;
x_1066 = x_1163;
x_1067 = x_1233;
x_1068 = x_1164;
x_1069 = x_1165;
goto block_1083;
}
}
}
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; uint8_t x_1238; 
lean_dec(x_1177);
x_1234 = lean_unsigned_to_nat(4u);
x_1235 = l_Lean_Syntax_getArg(x_1, x_1234);
x_1236 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_5);
lean_inc(x_4);
x_1237 = l_Lean_Name_mkStr3(x_4, x_5, x_1236);
lean_inc(x_1235);
x_1238 = l_Lean_Syntax_isOfKind(x_1235, x_1237);
if (x_1238 == 0)
{
lean_object* x_1239; 
lean_dec(x_1237);
lean_dec(x_1235);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1239 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1239;
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; uint8_t x_1243; 
x_1240 = l_Lean_Syntax_getArg(x_1235, x_1162);
lean_dec(x_1235);
x_1241 = lean_unsigned_to_nat(5u);
x_1242 = l_Lean_Syntax_getArg(x_1, x_1241);
x_1243 = l_Lean_Syntax_isNone(x_1242);
if (x_1243 == 0)
{
uint8_t x_1244; 
lean_inc(x_1242);
x_1244 = l_Lean_Syntax_matchesNull(x_1242, x_1162);
if (x_1244 == 0)
{
lean_object* x_1245; 
lean_dec(x_1242);
lean_dec(x_1240);
lean_dec(x_1237);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1245 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1245;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; uint8_t x_1249; 
x_1246 = l_Lean_Syntax_getArg(x_1242, x_1031);
lean_dec(x_1242);
x_1247 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1248 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1247);
lean_inc(x_1246);
x_1249 = l_Lean_Syntax_isOfKind(x_1246, x_1248);
lean_dec(x_1248);
if (x_1249 == 0)
{
lean_object* x_1250; 
lean_dec(x_1246);
lean_dec(x_1240);
lean_dec(x_1237);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1250 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1250;
}
else
{
lean_object* x_1251; lean_object* x_1252; 
x_1251 = l_Lean_Syntax_getArg(x_1246, x_1176);
lean_dec(x_1246);
x_1252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1252, 0, x_1251);
x_1084 = x_1237;
x_1085 = x_1161;
x_1086 = x_1176;
x_1087 = x_1168;
x_1088 = x_1170;
x_1089 = x_1183;
x_1090 = x_1162;
x_1091 = x_1163;
x_1092 = x_1240;
x_1093 = x_1252;
x_1094 = x_1164;
x_1095 = x_1165;
goto block_1109;
}
}
}
else
{
lean_object* x_1253; 
lean_dec(x_1242);
x_1253 = lean_box(0);
x_1084 = x_1237;
x_1085 = x_1161;
x_1086 = x_1176;
x_1087 = x_1168;
x_1088 = x_1170;
x_1089 = x_1183;
x_1090 = x_1162;
x_1091 = x_1163;
x_1092 = x_1240;
x_1093 = x_1253;
x_1094 = x_1164;
x_1095 = x_1165;
goto block_1109;
}
}
}
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; uint8_t x_1258; 
lean_dec(x_1177);
x_1254 = lean_unsigned_to_nat(4u);
x_1255 = l_Lean_Syntax_getArg(x_1, x_1254);
x_1256 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_5);
lean_inc(x_4);
x_1257 = l_Lean_Name_mkStr3(x_4, x_5, x_1256);
lean_inc(x_1255);
x_1258 = l_Lean_Syntax_isOfKind(x_1255, x_1257);
if (x_1258 == 0)
{
lean_object* x_1259; 
lean_dec(x_1257);
lean_dec(x_1255);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1259 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1259;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; uint8_t x_1263; 
x_1260 = l_Lean_Syntax_getArg(x_1255, x_1162);
lean_dec(x_1255);
x_1261 = lean_unsigned_to_nat(5u);
x_1262 = l_Lean_Syntax_getArg(x_1, x_1261);
x_1263 = l_Lean_Syntax_isNone(x_1262);
if (x_1263 == 0)
{
uint8_t x_1264; 
lean_inc(x_1262);
x_1264 = l_Lean_Syntax_matchesNull(x_1262, x_1162);
if (x_1264 == 0)
{
lean_object* x_1265; 
lean_dec(x_1262);
lean_dec(x_1260);
lean_dec(x_1257);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1265 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1265;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; 
x_1266 = l_Lean_Syntax_getArg(x_1262, x_1031);
lean_dec(x_1262);
x_1267 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1268 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1267);
lean_inc(x_1266);
x_1269 = l_Lean_Syntax_isOfKind(x_1266, x_1268);
lean_dec(x_1268);
if (x_1269 == 0)
{
lean_object* x_1270; 
lean_dec(x_1266);
lean_dec(x_1260);
lean_dec(x_1257);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1270 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1270;
}
else
{
lean_object* x_1271; lean_object* x_1272; 
x_1271 = l_Lean_Syntax_getArg(x_1266, x_1176);
lean_dec(x_1266);
x_1272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1272, 0, x_1271);
x_1110 = x_1161;
x_1111 = x_1176;
x_1112 = x_1168;
x_1113 = x_1260;
x_1114 = x_1170;
x_1115 = x_1162;
x_1116 = x_1163;
x_1117 = x_1257;
x_1118 = x_1180;
x_1119 = x_1272;
x_1120 = x_1164;
x_1121 = x_1165;
goto block_1135;
}
}
}
else
{
lean_object* x_1273; 
lean_dec(x_1262);
x_1273 = lean_box(0);
x_1110 = x_1161;
x_1111 = x_1176;
x_1112 = x_1168;
x_1113 = x_1260;
x_1114 = x_1170;
x_1115 = x_1162;
x_1116 = x_1163;
x_1117 = x_1257;
x_1118 = x_1180;
x_1119 = x_1273;
x_1120 = x_1164;
x_1121 = x_1165;
goto block_1135;
}
}
}
}
else
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; uint8_t x_1278; 
lean_dec(x_1177);
x_1274 = lean_unsigned_to_nat(4u);
x_1275 = l_Lean_Syntax_getArg(x_1, x_1274);
x_1276 = lean_mk_string_unchecked("precedence", 10, 10);
lean_inc(x_5);
lean_inc(x_4);
x_1277 = l_Lean_Name_mkStr3(x_4, x_5, x_1276);
lean_inc(x_1275);
x_1278 = l_Lean_Syntax_isOfKind(x_1275, x_1277);
if (x_1278 == 0)
{
lean_object* x_1279; 
lean_dec(x_1277);
lean_dec(x_1275);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1279 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1279;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; uint8_t x_1283; 
x_1280 = l_Lean_Syntax_getArg(x_1275, x_1162);
lean_dec(x_1275);
x_1281 = lean_unsigned_to_nat(5u);
x_1282 = l_Lean_Syntax_getArg(x_1, x_1281);
x_1283 = l_Lean_Syntax_isNone(x_1282);
if (x_1283 == 0)
{
uint8_t x_1284; 
lean_inc(x_1282);
x_1284 = l_Lean_Syntax_matchesNull(x_1282, x_1162);
if (x_1284 == 0)
{
lean_object* x_1285; 
lean_dec(x_1282);
lean_dec(x_1280);
lean_dec(x_1277);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1285 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1285;
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; uint8_t x_1289; 
x_1286 = l_Lean_Syntax_getArg(x_1282, x_1031);
lean_dec(x_1282);
x_1287 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1288 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1287);
lean_inc(x_1286);
x_1289 = l_Lean_Syntax_isOfKind(x_1286, x_1288);
lean_dec(x_1288);
if (x_1289 == 0)
{
lean_object* x_1290; 
lean_dec(x_1286);
lean_dec(x_1280);
lean_dec(x_1277);
lean_dec(x_1170);
lean_dec(x_1168);
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1290 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1164, x_1165);
lean_dec(x_1164);
return x_1290;
}
else
{
lean_object* x_1291; lean_object* x_1292; 
x_1291 = l_Lean_Syntax_getArg(x_1286, x_1176);
lean_dec(x_1286);
x_1292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1292, 0, x_1291);
x_1136 = x_1161;
x_1137 = x_1176;
x_1138 = x_1168;
x_1139 = x_1170;
x_1140 = x_1280;
x_1141 = x_1162;
x_1142 = x_1163;
x_1143 = x_1277;
x_1144 = x_1292;
x_1145 = x_1164;
x_1146 = x_1165;
goto block_1160;
}
}
}
else
{
lean_object* x_1293; 
lean_dec(x_1282);
x_1293 = lean_box(0);
x_1136 = x_1161;
x_1137 = x_1176;
x_1138 = x_1168;
x_1139 = x_1170;
x_1140 = x_1280;
x_1141 = x_1162;
x_1142 = x_1163;
x_1143 = x_1277;
x_1144 = x_1293;
x_1145 = x_1164;
x_1146 = x_1165;
goto block_1160;
}
}
}
}
}
}
block_1313:
{
lean_object* x_1298; lean_object* x_1299; uint8_t x_1300; 
x_1298 = lean_unsigned_to_nat(1u);
x_1299 = l_Lean_Syntax_getArg(x_1, x_1298);
x_1300 = l_Lean_Syntax_isNone(x_1299);
if (x_1300 == 0)
{
uint8_t x_1301; 
lean_inc(x_1299);
x_1301 = l_Lean_Syntax_matchesNull(x_1299, x_1298);
if (x_1301 == 0)
{
lean_object* x_1302; 
lean_dec(x_1299);
lean_dec(x_1295);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1302 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1296, x_1297);
lean_dec(x_1296);
return x_1302;
}
else
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; uint8_t x_1307; 
x_1303 = l_Lean_Syntax_getArg(x_1299, x_1031);
lean_dec(x_1299);
x_1304 = lean_mk_string_unchecked("Term", 4, 4);
x_1305 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_5);
lean_inc(x_4);
x_1306 = l_Lean_Name_mkStr4(x_4, x_5, x_1304, x_1305);
lean_inc(x_1303);
x_1307 = l_Lean_Syntax_isOfKind(x_1303, x_1306);
lean_dec(x_1306);
if (x_1307 == 0)
{
lean_object* x_1308; 
lean_dec(x_1303);
lean_dec(x_1295);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1308 = l_Lean_Macro_throwUnsupported(lean_box(0), x_1296, x_1297);
lean_dec(x_1296);
return x_1308;
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
x_1309 = l_Lean_Syntax_getArg(x_1303, x_1298);
lean_dec(x_1303);
x_1310 = l_Lean_Syntax_getArgs(x_1309);
lean_dec(x_1309);
x_1311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1311, 0, x_1310);
x_1161 = x_1295;
x_1162 = x_1298;
x_1163 = x_1311;
x_1164 = x_1296;
x_1165 = x_1297;
goto block_1294;
}
}
}
else
{
lean_object* x_1312; 
lean_dec(x_1299);
x_1312 = lean_box(0);
x_1161 = x_1295;
x_1162 = x_1298;
x_1163 = x_1312;
x_1164 = x_1296;
x_1165 = x_1297;
goto block_1294;
}
}
}
block_56:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_24 = l_Array_append(lean_box(0), x_18, x_23);
lean_dec(x_23);
lean_inc(x_19);
lean_inc(x_20);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_mk_string_unchecked("identPrec", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_26);
x_28 = lean_mk_string_unchecked("arg", 3, 3);
lean_inc(x_28);
x_29 = l_String_toSubstring_x27(x_28);
x_30 = l_Lean_Name_mkStr1(x_28);
x_31 = l_Lean_addMacroScope(x_16, x_30, x_12);
x_32 = lean_box(0);
lean_inc(x_20);
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
lean_inc(x_15);
lean_inc(x_33);
lean_inc(x_20);
x_34 = l_Lean_Syntax_node2(x_20, x_27, x_33, x_15);
lean_inc(x_19);
lean_inc(x_20);
x_35 = l_Lean_Syntax_node2(x_20, x_19, x_34, x_22);
x_36 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_20);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("app", 3, 3);
x_39 = l_Lean_Name_mkStr4(x_4, x_5, x_10, x_38);
lean_inc(x_20);
x_40 = l_Lean_Syntax_node1(x_20, x_19, x_33);
lean_inc(x_20);
x_41 = l_Lean_Syntax_node2(x_20, x_39, x_11, x_40);
x_42 = lean_unsigned_to_nat(10u);
x_43 = lean_mk_empty_array_with_capacity(x_42);
x_44 = lean_array_push(x_43, x_17);
x_45 = lean_array_push(x_44, x_9);
x_46 = lean_array_push(x_45, x_8);
x_47 = lean_array_push(x_46, x_14);
x_48 = lean_array_push(x_47, x_15);
x_49 = lean_array_push(x_48, x_21);
x_50 = lean_array_push(x_49, x_25);
x_51 = lean_array_push(x_50, x_35);
x_52 = lean_array_push(x_51, x_37);
x_53 = lean_array_push(x_52, x_41);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_13);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
return x_55;
}
block_90:
{
lean_object* x_74; lean_object* x_75; 
lean_inc(x_68);
x_74 = l_Array_append(lean_box(0), x_68, x_73);
lean_dec(x_73);
lean_inc(x_69);
lean_inc(x_71);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_69);
lean_ctor_set(x_75, 2, x_74);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_76; 
x_76 = l_Array_empty(lean_box(0));
x_7 = x_57;
x_8 = x_58;
x_9 = x_59;
x_10 = x_60;
x_11 = x_61;
x_12 = x_62;
x_13 = x_63;
x_14 = x_64;
x_15 = x_65;
x_16 = x_66;
x_17 = x_67;
x_18 = x_68;
x_19 = x_69;
x_20 = x_71;
x_21 = x_75;
x_22 = x_72;
x_23 = x_76;
goto block_56;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_70, 0);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_79 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_78);
x_80 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_71);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_71);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_71);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_71);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_71);
lean_ctor_set(x_87, 1, x_86);
lean_inc(x_71);
x_88 = l_Lean_Syntax_node5(x_71, x_79, x_81, x_83, x_85, x_77, x_87);
x_89 = l_Array_mkArray1___redArg(x_88);
x_7 = x_57;
x_8 = x_58;
x_9 = x_59;
x_10 = x_60;
x_11 = x_61;
x_12 = x_62;
x_13 = x_63;
x_14 = x_64;
x_15 = x_65;
x_16 = x_66;
x_17 = x_67;
x_18 = x_68;
x_19 = x_69;
x_20 = x_71;
x_21 = x_75;
x_22 = x_72;
x_23 = x_89;
goto block_56;
}
}
block_132:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_inc(x_100);
x_109 = l_Array_append(lean_box(0), x_100, x_108);
lean_dec(x_108);
lean_inc(x_101);
lean_inc(x_105);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_109);
lean_inc(x_100);
lean_inc(x_101);
lean_inc(x_105);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_101);
lean_ctor_set(x_111, 2, x_100);
lean_inc(x_105);
x_112 = l_Lean_Syntax_node1(x_105, x_95, x_111);
lean_inc(x_105);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_103);
x_114 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_105);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_114);
lean_inc(x_105);
x_116 = l_Lean_Syntax_node2(x_105, x_104, x_115, x_107);
lean_inc(x_101);
lean_inc(x_105);
x_117 = l_Lean_Syntax_node1(x_105, x_101, x_116);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_118; 
x_118 = l_Array_empty(lean_box(0));
x_57 = x_91;
x_58 = x_112;
x_59 = x_110;
x_60 = x_92;
x_61 = x_93;
x_62 = x_94;
x_63 = x_96;
x_64 = x_113;
x_65 = x_117;
x_66 = x_98;
x_67 = x_99;
x_68 = x_100;
x_69 = x_101;
x_70 = x_102;
x_71 = x_105;
x_72 = x_106;
x_73 = x_118;
goto block_90;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_119 = lean_ctor_get(x_97, 0);
lean_inc(x_119);
lean_dec(x_97);
x_120 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_121 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_120);
x_122 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_105);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_105);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_105);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_105);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_105);
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_105);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_105);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_105);
lean_ctor_set(x_129, 1, x_128);
lean_inc(x_105);
x_130 = l_Lean_Syntax_node5(x_105, x_121, x_123, x_125, x_127, x_119, x_129);
x_131 = l_Array_mkArray1___redArg(x_130);
x_57 = x_91;
x_58 = x_112;
x_59 = x_110;
x_60 = x_92;
x_61 = x_93;
x_62 = x_94;
x_63 = x_96;
x_64 = x_113;
x_65 = x_117;
x_66 = x_98;
x_67 = x_99;
x_68 = x_100;
x_69 = x_101;
x_70 = x_102;
x_71 = x_105;
x_72 = x_106;
x_73 = x_131;
goto block_90;
}
}
block_165:
{
lean_object* x_151; lean_object* x_152; 
lean_inc(x_142);
x_151 = l_Array_append(lean_box(0), x_142, x_150);
lean_dec(x_150);
lean_inc(x_143);
lean_inc(x_147);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_143);
lean_ctor_set(x_152, 2, x_151);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_153; 
x_153 = l_Array_empty(lean_box(0));
x_91 = x_133;
x_92 = x_134;
x_93 = x_135;
x_94 = x_136;
x_95 = x_137;
x_96 = x_138;
x_97 = x_140;
x_98 = x_141;
x_99 = x_152;
x_100 = x_142;
x_101 = x_143;
x_102 = x_144;
x_103 = x_146;
x_104 = x_145;
x_105 = x_147;
x_106 = x_148;
x_107 = x_149;
x_108 = x_153;
goto block_132;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_139, 0);
lean_inc(x_154);
lean_dec(x_139);
x_155 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_134);
lean_inc(x_5);
lean_inc(x_4);
x_156 = l_Lean_Name_mkStr4(x_4, x_5, x_134, x_155);
x_157 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_147);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_157);
lean_inc(x_142);
x_159 = l_Array_append(lean_box(0), x_142, x_154);
lean_dec(x_154);
lean_inc(x_143);
lean_inc(x_147);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_143);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_147);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_147);
x_163 = l_Lean_Syntax_node3(x_147, x_156, x_158, x_160, x_162);
x_164 = l_Array_mkArray1___redArg(x_163);
x_91 = x_133;
x_92 = x_134;
x_93 = x_135;
x_94 = x_136;
x_95 = x_137;
x_96 = x_138;
x_97 = x_140;
x_98 = x_141;
x_99 = x_152;
x_100 = x_142;
x_101 = x_143;
x_102 = x_144;
x_103 = x_146;
x_104 = x_145;
x_105 = x_147;
x_106 = x_148;
x_107 = x_149;
x_108 = x_164;
goto block_132;
}
}
block_215:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_183 = l_Array_append(lean_box(0), x_170, x_182);
lean_dec(x_182);
lean_inc(x_166);
lean_inc(x_181);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_166);
lean_ctor_set(x_184, 2, x_183);
x_185 = lean_mk_string_unchecked("identPrec", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
x_186 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_185);
x_187 = lean_mk_string_unchecked("arg", 3, 3);
lean_inc(x_187);
x_188 = l_String_toSubstring_x27(x_187);
x_189 = l_Lean_Name_mkStr1(x_187);
x_190 = l_Lean_addMacroScope(x_178, x_189, x_177);
x_191 = lean_box(0);
lean_inc(x_181);
x_192 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_192, 0, x_181);
lean_ctor_set(x_192, 1, x_188);
lean_ctor_set(x_192, 2, x_190);
lean_ctor_set(x_192, 3, x_191);
lean_inc(x_176);
lean_inc(x_192);
lean_inc(x_181);
x_193 = l_Lean_Syntax_node2(x_181, x_186, x_192, x_176);
lean_inc(x_166);
lean_inc(x_181);
x_194 = l_Lean_Syntax_node2(x_181, x_166, x_169, x_193);
x_195 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_181);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_181);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_mk_string_unchecked("app", 3, 3);
x_198 = l_Lean_Name_mkStr4(x_4, x_5, x_168, x_197);
lean_inc(x_181);
x_199 = l_Lean_Syntax_node1(x_181, x_166, x_192);
lean_inc(x_181);
x_200 = l_Lean_Syntax_node2(x_181, x_198, x_174, x_199);
x_201 = lean_unsigned_to_nat(10u);
x_202 = lean_mk_empty_array_with_capacity(x_201);
x_203 = lean_array_push(x_202, x_180);
x_204 = lean_array_push(x_203, x_175);
x_205 = lean_array_push(x_204, x_167);
x_206 = lean_array_push(x_205, x_172);
x_207 = lean_array_push(x_206, x_176);
x_208 = lean_array_push(x_207, x_179);
x_209 = lean_array_push(x_208, x_184);
x_210 = lean_array_push(x_209, x_194);
x_211 = lean_array_push(x_210, x_196);
x_212 = lean_array_push(x_211, x_200);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_181);
lean_ctor_set(x_213, 1, x_171);
lean_ctor_set(x_213, 2, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_173);
return x_214;
}
block_249:
{
lean_object* x_233; lean_object* x_234; 
lean_inc(x_221);
x_233 = l_Array_append(lean_box(0), x_221, x_232);
lean_dec(x_232);
lean_inc(x_216);
lean_inc(x_231);
x_234 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_216);
lean_ctor_set(x_234, 2, x_233);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_235; 
x_235 = l_Array_empty(lean_box(0));
x_166 = x_216;
x_167 = x_217;
x_168 = x_218;
x_169 = x_219;
x_170 = x_221;
x_171 = x_222;
x_172 = x_223;
x_173 = x_224;
x_174 = x_225;
x_175 = x_226;
x_176 = x_227;
x_177 = x_228;
x_178 = x_229;
x_179 = x_234;
x_180 = x_230;
x_181 = x_231;
x_182 = x_235;
goto block_215;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_236 = lean_ctor_get(x_220, 0);
lean_inc(x_236);
lean_dec(x_220);
x_237 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_238 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_237);
x_239 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_231);
x_240 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_240, 0, x_231);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_231);
x_242 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_242, 0, x_231);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_231);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_231);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_231);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_231);
lean_ctor_set(x_246, 1, x_245);
lean_inc(x_231);
x_247 = l_Lean_Syntax_node5(x_231, x_238, x_240, x_242, x_244, x_236, x_246);
x_248 = l_Array_mkArray1___redArg(x_247);
x_166 = x_216;
x_167 = x_217;
x_168 = x_218;
x_169 = x_219;
x_170 = x_221;
x_171 = x_222;
x_172 = x_223;
x_173 = x_224;
x_174 = x_225;
x_175 = x_226;
x_176 = x_227;
x_177 = x_228;
x_178 = x_229;
x_179 = x_234;
x_180 = x_230;
x_181 = x_231;
x_182 = x_248;
goto block_215;
}
}
block_291:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_inc(x_256);
x_268 = l_Array_append(lean_box(0), x_256, x_267);
lean_dec(x_267);
lean_inc(x_251);
lean_inc(x_266);
x_269 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_251);
lean_ctor_set(x_269, 2, x_268);
lean_inc(x_256);
lean_inc(x_251);
lean_inc(x_266);
x_270 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_251);
lean_ctor_set(x_270, 2, x_256);
lean_inc(x_266);
x_271 = l_Lean_Syntax_node1(x_266, x_254, x_270);
lean_inc(x_266);
x_272 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_272, 0, x_266);
lean_ctor_set(x_272, 1, x_258);
x_273 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_266);
x_274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_274, 0, x_266);
lean_ctor_set(x_274, 1, x_273);
lean_inc(x_266);
x_275 = l_Lean_Syntax_node2(x_266, x_261, x_274, x_263);
lean_inc(x_251);
lean_inc(x_266);
x_276 = l_Lean_Syntax_node1(x_266, x_251, x_275);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_277; 
x_277 = l_Array_empty(lean_box(0));
x_216 = x_251;
x_217 = x_271;
x_218 = x_252;
x_219 = x_253;
x_220 = x_255;
x_221 = x_256;
x_222 = x_257;
x_223 = x_272;
x_224 = x_259;
x_225 = x_260;
x_226 = x_269;
x_227 = x_276;
x_228 = x_262;
x_229 = x_264;
x_230 = x_265;
x_231 = x_266;
x_232 = x_277;
goto block_249;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_278 = lean_ctor_get(x_250, 0);
lean_inc(x_278);
lean_dec(x_250);
x_279 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_280 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_279);
x_281 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_266);
x_282 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_282, 0, x_266);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_266);
x_284 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_284, 0, x_266);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_266);
x_286 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_286, 0, x_266);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_266);
x_288 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_288, 0, x_266);
lean_ctor_set(x_288, 1, x_287);
lean_inc(x_266);
x_289 = l_Lean_Syntax_node5(x_266, x_280, x_282, x_284, x_286, x_278, x_288);
x_290 = l_Array_mkArray1___redArg(x_289);
x_216 = x_251;
x_217 = x_271;
x_218 = x_252;
x_219 = x_253;
x_220 = x_255;
x_221 = x_256;
x_222 = x_257;
x_223 = x_272;
x_224 = x_259;
x_225 = x_260;
x_226 = x_269;
x_227 = x_276;
x_228 = x_262;
x_229 = x_264;
x_230 = x_265;
x_231 = x_266;
x_232 = x_290;
goto block_249;
}
}
block_324:
{
lean_object* x_310; lean_object* x_311; 
lean_inc(x_299);
x_310 = l_Array_append(lean_box(0), x_299, x_309);
lean_dec(x_309);
lean_inc(x_293);
lean_inc(x_308);
x_311 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_293);
lean_ctor_set(x_311, 2, x_310);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_312; 
x_312 = l_Array_empty(lean_box(0));
x_250 = x_292;
x_251 = x_293;
x_252 = x_294;
x_253 = x_295;
x_254 = x_296;
x_255 = x_297;
x_256 = x_299;
x_257 = x_300;
x_258 = x_301;
x_259 = x_302;
x_260 = x_303;
x_261 = x_304;
x_262 = x_306;
x_263 = x_305;
x_264 = x_307;
x_265 = x_311;
x_266 = x_308;
x_267 = x_312;
goto block_291;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_313 = lean_ctor_get(x_298, 0);
lean_inc(x_313);
lean_dec(x_298);
x_314 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_294);
lean_inc(x_5);
lean_inc(x_4);
x_315 = l_Lean_Name_mkStr4(x_4, x_5, x_294, x_314);
x_316 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_308);
x_317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_317, 0, x_308);
lean_ctor_set(x_317, 1, x_316);
lean_inc(x_299);
x_318 = l_Array_append(lean_box(0), x_299, x_313);
lean_dec(x_313);
lean_inc(x_293);
lean_inc(x_308);
x_319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_319, 0, x_308);
lean_ctor_set(x_319, 1, x_293);
lean_ctor_set(x_319, 2, x_318);
x_320 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_308);
x_321 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_321, 0, x_308);
lean_ctor_set(x_321, 1, x_320);
lean_inc(x_308);
x_322 = l_Lean_Syntax_node3(x_308, x_315, x_317, x_319, x_321);
x_323 = l_Array_mkArray1___redArg(x_322);
x_250 = x_292;
x_251 = x_293;
x_252 = x_294;
x_253 = x_295;
x_254 = x_296;
x_255 = x_297;
x_256 = x_299;
x_257 = x_300;
x_258 = x_301;
x_259 = x_302;
x_260 = x_303;
x_261 = x_304;
x_262 = x_306;
x_263 = x_305;
x_264 = x_307;
x_265 = x_311;
x_266 = x_308;
x_267 = x_323;
goto block_291;
}
}
block_385:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_345 = l_Array_append(lean_box(0), x_330, x_344);
lean_dec(x_344);
lean_inc(x_341);
lean_inc(x_343);
x_346 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_341);
lean_ctor_set(x_346, 2, x_345);
x_347 = lean_mk_string_unchecked("identPrec", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
x_348 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_347);
x_349 = lean_mk_string_unchecked("lhs", 3, 3);
lean_inc(x_349);
x_350 = l_String_toSubstring_x27(x_349);
x_351 = l_Lean_Name_mkStr1(x_349);
lean_inc(x_339);
lean_inc(x_335);
x_352 = l_Lean_addMacroScope(x_335, x_351, x_339);
x_353 = lean_box(0);
lean_inc(x_343);
x_354 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_354, 0, x_343);
lean_ctor_set(x_354, 1, x_350);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_353);
lean_inc(x_343);
x_355 = l_Lean_Syntax_node2(x_343, x_325, x_336, x_337);
lean_inc(x_341);
lean_inc(x_343);
x_356 = l_Lean_Syntax_node1(x_343, x_341, x_355);
lean_inc(x_354);
lean_inc(x_348);
lean_inc(x_343);
x_357 = l_Lean_Syntax_node2(x_343, x_348, x_354, x_356);
x_358 = lean_mk_string_unchecked("rhs", 3, 3);
lean_inc(x_358);
x_359 = l_String_toSubstring_x27(x_358);
x_360 = l_Lean_Name_mkStr1(x_358);
x_361 = l_Lean_addMacroScope(x_335, x_360, x_339);
lean_inc(x_343);
x_362 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_362, 0, x_343);
lean_ctor_set(x_362, 1, x_359);
lean_ctor_set(x_362, 2, x_361);
lean_ctor_set(x_362, 3, x_353);
lean_inc(x_326);
lean_inc(x_362);
lean_inc(x_343);
x_363 = l_Lean_Syntax_node2(x_343, x_348, x_362, x_326);
lean_inc(x_341);
lean_inc(x_343);
x_364 = l_Lean_Syntax_node3(x_343, x_341, x_357, x_327, x_363);
x_365 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_343);
x_366 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_366, 0, x_343);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_mk_string_unchecked("app", 3, 3);
x_368 = l_Lean_Name_mkStr4(x_4, x_5, x_328, x_367);
lean_inc(x_343);
x_369 = l_Lean_Syntax_node2(x_343, x_341, x_354, x_362);
lean_inc(x_343);
x_370 = l_Lean_Syntax_node2(x_343, x_368, x_334, x_369);
x_371 = lean_unsigned_to_nat(10u);
x_372 = lean_mk_empty_array_with_capacity(x_371);
x_373 = lean_array_push(x_372, x_329);
x_374 = lean_array_push(x_373, x_332);
x_375 = lean_array_push(x_374, x_340);
x_376 = lean_array_push(x_375, x_333);
x_377 = lean_array_push(x_376, x_326);
x_378 = lean_array_push(x_377, x_331);
x_379 = lean_array_push(x_378, x_346);
x_380 = lean_array_push(x_379, x_364);
x_381 = lean_array_push(x_380, x_366);
x_382 = lean_array_push(x_381, x_370);
x_383 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_383, 0, x_343);
lean_ctor_set(x_383, 1, x_338);
lean_ctor_set(x_383, 2, x_382);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_342);
return x_384;
}
block_422:
{
lean_object* x_406; lean_object* x_407; 
lean_inc(x_392);
x_406 = l_Array_append(lean_box(0), x_392, x_405);
lean_dec(x_405);
lean_inc(x_402);
lean_inc(x_404);
x_407 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_402);
lean_ctor_set(x_407, 2, x_406);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_408; 
x_408 = l_Array_empty(lean_box(0));
x_325 = x_386;
x_326 = x_388;
x_327 = x_389;
x_328 = x_390;
x_329 = x_391;
x_330 = x_392;
x_331 = x_407;
x_332 = x_393;
x_333 = x_394;
x_334 = x_395;
x_335 = x_396;
x_336 = x_398;
x_337 = x_397;
x_338 = x_400;
x_339 = x_399;
x_340 = x_401;
x_341 = x_402;
x_342 = x_403;
x_343 = x_404;
x_344 = x_408;
goto block_385;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_409 = lean_ctor_get(x_387, 0);
lean_inc(x_409);
lean_dec(x_387);
x_410 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_411 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_410);
x_412 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_404);
x_413 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_413, 0, x_404);
lean_ctor_set(x_413, 1, x_412);
x_414 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_404);
x_415 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_415, 0, x_404);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_404);
x_417 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_417, 0, x_404);
lean_ctor_set(x_417, 1, x_416);
x_418 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_404);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_404);
lean_ctor_set(x_419, 1, x_418);
lean_inc(x_404);
x_420 = l_Lean_Syntax_node5(x_404, x_411, x_413, x_415, x_417, x_409, x_419);
x_421 = l_Array_mkArray1___redArg(x_420);
x_325 = x_386;
x_326 = x_388;
x_327 = x_389;
x_328 = x_390;
x_329 = x_391;
x_330 = x_392;
x_331 = x_407;
x_332 = x_393;
x_333 = x_394;
x_334 = x_395;
x_335 = x_396;
x_336 = x_398;
x_337 = x_397;
x_338 = x_400;
x_339 = x_399;
x_340 = x_401;
x_341 = x_402;
x_342 = x_403;
x_343 = x_404;
x_344 = x_421;
goto block_385;
}
}
block_465:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_inc(x_430);
x_442 = l_Array_append(lean_box(0), x_430, x_441);
lean_dec(x_441);
lean_inc(x_436);
lean_inc(x_438);
x_443 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_443, 0, x_438);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_442);
lean_inc(x_430);
lean_inc(x_436);
lean_inc(x_438);
x_444 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_444, 0, x_438);
lean_ctor_set(x_444, 1, x_436);
lean_ctor_set(x_444, 2, x_430);
lean_inc(x_438);
x_445 = l_Lean_Syntax_node1(x_438, x_427, x_444);
lean_inc(x_438);
x_446 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_446, 0, x_438);
lean_ctor_set(x_446, 1, x_439);
x_447 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_438);
x_448 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_448, 0, x_438);
lean_ctor_set(x_448, 1, x_447);
lean_inc(x_448);
lean_inc(x_423);
lean_inc(x_438);
x_449 = l_Lean_Syntax_node2(x_438, x_423, x_448, x_440);
lean_inc(x_436);
lean_inc(x_438);
x_450 = l_Lean_Syntax_node1(x_438, x_436, x_449);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_451; 
x_451 = l_Array_empty(lean_box(0));
x_386 = x_423;
x_387 = x_424;
x_388 = x_450;
x_389 = x_425;
x_390 = x_426;
x_391 = x_428;
x_392 = x_430;
x_393 = x_443;
x_394 = x_446;
x_395 = x_431;
x_396 = x_432;
x_397 = x_433;
x_398 = x_448;
x_399 = x_435;
x_400 = x_434;
x_401 = x_445;
x_402 = x_436;
x_403 = x_437;
x_404 = x_438;
x_405 = x_451;
goto block_422;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_452 = lean_ctor_get(x_429, 0);
lean_inc(x_452);
lean_dec(x_429);
x_453 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_454 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_453);
x_455 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_438);
x_456 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_456, 0, x_438);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_438);
x_458 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_458, 0, x_438);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_438);
x_460 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_460, 0, x_438);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_438);
x_462 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_462, 0, x_438);
lean_ctor_set(x_462, 1, x_461);
lean_inc(x_438);
x_463 = l_Lean_Syntax_node5(x_438, x_454, x_456, x_458, x_460, x_452, x_462);
x_464 = l_Array_mkArray1___redArg(x_463);
x_386 = x_423;
x_387 = x_424;
x_388 = x_450;
x_389 = x_425;
x_390 = x_426;
x_391 = x_428;
x_392 = x_430;
x_393 = x_443;
x_394 = x_446;
x_395 = x_431;
x_396 = x_432;
x_397 = x_433;
x_398 = x_448;
x_399 = x_435;
x_400 = x_434;
x_401 = x_445;
x_402 = x_436;
x_403 = x_437;
x_404 = x_438;
x_405 = x_464;
goto block_422;
}
}
block_499:
{
lean_object* x_485; lean_object* x_486; 
lean_inc(x_472);
x_485 = l_Array_append(lean_box(0), x_472, x_484);
lean_dec(x_484);
lean_inc(x_479);
lean_inc(x_481);
x_486 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_479);
lean_ctor_set(x_486, 2, x_485);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_487; 
x_487 = l_Array_empty(lean_box(0));
x_423 = x_466;
x_424 = x_467;
x_425 = x_468;
x_426 = x_469;
x_427 = x_470;
x_428 = x_486;
x_429 = x_471;
x_430 = x_472;
x_431 = x_474;
x_432 = x_475;
x_433 = x_476;
x_434 = x_478;
x_435 = x_477;
x_436 = x_479;
x_437 = x_480;
x_438 = x_481;
x_439 = x_482;
x_440 = x_483;
x_441 = x_487;
goto block_465;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_488 = lean_ctor_get(x_473, 0);
lean_inc(x_488);
lean_dec(x_473);
x_489 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_469);
lean_inc(x_5);
lean_inc(x_4);
x_490 = l_Lean_Name_mkStr4(x_4, x_5, x_469, x_489);
x_491 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_481);
x_492 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_492, 0, x_481);
lean_ctor_set(x_492, 1, x_491);
lean_inc(x_472);
x_493 = l_Array_append(lean_box(0), x_472, x_488);
lean_dec(x_488);
lean_inc(x_479);
lean_inc(x_481);
x_494 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_494, 0, x_481);
lean_ctor_set(x_494, 1, x_479);
lean_ctor_set(x_494, 2, x_493);
x_495 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_481);
x_496 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_496, 0, x_481);
lean_ctor_set(x_496, 1, x_495);
lean_inc(x_481);
x_497 = l_Lean_Syntax_node3(x_481, x_490, x_492, x_494, x_496);
x_498 = l_Array_mkArray1___redArg(x_497);
x_423 = x_466;
x_424 = x_467;
x_425 = x_468;
x_426 = x_469;
x_427 = x_470;
x_428 = x_486;
x_429 = x_471;
x_430 = x_472;
x_431 = x_474;
x_432 = x_475;
x_433 = x_476;
x_434 = x_478;
x_435 = x_477;
x_436 = x_479;
x_437 = x_480;
x_438 = x_481;
x_439 = x_482;
x_440 = x_483;
x_441 = x_498;
goto block_465;
}
}
block_560:
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_520 = l_Array_append(lean_box(0), x_514, x_519);
lean_dec(x_519);
lean_inc(x_512);
lean_inc(x_515);
x_521 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_521, 0, x_515);
lean_ctor_set(x_521, 1, x_512);
lean_ctor_set(x_521, 2, x_520);
x_522 = lean_mk_string_unchecked("identPrec", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
x_523 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_522);
x_524 = lean_mk_string_unchecked("lhs", 3, 3);
lean_inc(x_524);
x_525 = l_String_toSubstring_x27(x_524);
x_526 = l_Lean_Name_mkStr1(x_524);
lean_inc(x_516);
lean_inc(x_513);
x_527 = l_Lean_addMacroScope(x_513, x_526, x_516);
x_528 = lean_box(0);
lean_inc(x_515);
x_529 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_529, 0, x_515);
lean_ctor_set(x_529, 1, x_525);
lean_ctor_set(x_529, 2, x_527);
lean_ctor_set(x_529, 3, x_528);
lean_inc(x_515);
x_530 = l_Lean_Syntax_node2(x_515, x_507, x_518, x_509);
lean_inc(x_512);
lean_inc(x_515);
x_531 = l_Lean_Syntax_node1(x_515, x_512, x_530);
lean_inc(x_531);
lean_inc(x_529);
lean_inc(x_523);
lean_inc(x_515);
x_532 = l_Lean_Syntax_node2(x_515, x_523, x_529, x_531);
x_533 = lean_mk_string_unchecked("rhs", 3, 3);
lean_inc(x_533);
x_534 = l_String_toSubstring_x27(x_533);
x_535 = l_Lean_Name_mkStr1(x_533);
x_536 = l_Lean_addMacroScope(x_513, x_535, x_516);
lean_inc(x_515);
x_537 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_537, 0, x_515);
lean_ctor_set(x_537, 1, x_534);
lean_ctor_set(x_537, 2, x_536);
lean_ctor_set(x_537, 3, x_528);
lean_inc(x_537);
lean_inc(x_515);
x_538 = l_Lean_Syntax_node2(x_515, x_523, x_537, x_531);
lean_inc(x_512);
lean_inc(x_515);
x_539 = l_Lean_Syntax_node3(x_515, x_512, x_532, x_502, x_538);
x_540 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_515);
x_541 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_541, 0, x_515);
lean_ctor_set(x_541, 1, x_540);
x_542 = lean_mk_string_unchecked("app", 3, 3);
x_543 = l_Lean_Name_mkStr4(x_4, x_5, x_504, x_542);
lean_inc(x_515);
x_544 = l_Lean_Syntax_node2(x_515, x_512, x_529, x_537);
lean_inc(x_515);
x_545 = l_Lean_Syntax_node2(x_515, x_543, x_508, x_544);
x_546 = lean_unsigned_to_nat(10u);
x_547 = lean_mk_empty_array_with_capacity(x_546);
x_548 = lean_array_push(x_547, x_505);
x_549 = lean_array_push(x_548, x_506);
x_550 = lean_array_push(x_549, x_503);
x_551 = lean_array_push(x_550, x_517);
x_552 = lean_array_push(x_551, x_500);
x_553 = lean_array_push(x_552, x_511);
x_554 = lean_array_push(x_553, x_521);
x_555 = lean_array_push(x_554, x_539);
x_556 = lean_array_push(x_555, x_541);
x_557 = lean_array_push(x_556, x_545);
x_558 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_558, 0, x_515);
lean_ctor_set(x_558, 1, x_501);
lean_ctor_set(x_558, 2, x_557);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_510);
return x_559;
}
block_597:
{
lean_object* x_581; lean_object* x_582; 
lean_inc(x_575);
x_581 = l_Array_append(lean_box(0), x_575, x_580);
lean_dec(x_580);
lean_inc(x_574);
lean_inc(x_576);
x_582 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_582, 0, x_576);
lean_ctor_set(x_582, 1, x_574);
lean_ctor_set(x_582, 2, x_581);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_583; 
x_583 = l_Array_empty(lean_box(0));
x_500 = x_561;
x_501 = x_562;
x_502 = x_564;
x_503 = x_565;
x_504 = x_566;
x_505 = x_567;
x_506 = x_568;
x_507 = x_569;
x_508 = x_570;
x_509 = x_571;
x_510 = x_572;
x_511 = x_582;
x_512 = x_574;
x_513 = x_573;
x_514 = x_575;
x_515 = x_576;
x_516 = x_577;
x_517 = x_578;
x_518 = x_579;
x_519 = x_583;
goto block_560;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_584 = lean_ctor_get(x_563, 0);
lean_inc(x_584);
lean_dec(x_563);
x_585 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_586 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_585);
x_587 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_576);
x_588 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_588, 0, x_576);
lean_ctor_set(x_588, 1, x_587);
x_589 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_576);
x_590 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_590, 0, x_576);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_576);
x_592 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_592, 0, x_576);
lean_ctor_set(x_592, 1, x_591);
x_593 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_576);
x_594 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_594, 0, x_576);
lean_ctor_set(x_594, 1, x_593);
lean_inc(x_576);
x_595 = l_Lean_Syntax_node5(x_576, x_586, x_588, x_590, x_592, x_584, x_594);
x_596 = l_Array_mkArray1___redArg(x_595);
x_500 = x_561;
x_501 = x_562;
x_502 = x_564;
x_503 = x_565;
x_504 = x_566;
x_505 = x_567;
x_506 = x_568;
x_507 = x_569;
x_508 = x_570;
x_509 = x_571;
x_510 = x_572;
x_511 = x_582;
x_512 = x_574;
x_513 = x_573;
x_514 = x_575;
x_515 = x_576;
x_516 = x_577;
x_517 = x_578;
x_518 = x_579;
x_519 = x_596;
goto block_560;
}
}
block_640:
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_inc(x_611);
x_617 = l_Array_append(lean_box(0), x_611, x_616);
lean_dec(x_616);
lean_inc(x_610);
lean_inc(x_612);
x_618 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_618, 0, x_612);
lean_ctor_set(x_618, 1, x_610);
lean_ctor_set(x_618, 2, x_617);
lean_inc(x_611);
lean_inc(x_610);
lean_inc(x_612);
x_619 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_619, 0, x_612);
lean_ctor_set(x_619, 1, x_610);
lean_ctor_set(x_619, 2, x_611);
lean_inc(x_612);
x_620 = l_Lean_Syntax_node1(x_612, x_604, x_619);
lean_inc(x_612);
x_621 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_621, 0, x_612);
lean_ctor_set(x_621, 1, x_615);
x_622 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_612);
x_623 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_623, 0, x_612);
lean_ctor_set(x_623, 1, x_622);
lean_inc(x_623);
lean_inc(x_605);
lean_inc(x_612);
x_624 = l_Lean_Syntax_node2(x_612, x_605, x_623, x_603);
lean_inc(x_610);
lean_inc(x_612);
x_625 = l_Lean_Syntax_node1(x_612, x_610, x_624);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_626; 
x_626 = l_Array_empty(lean_box(0));
x_561 = x_625;
x_562 = x_598;
x_563 = x_599;
x_564 = x_600;
x_565 = x_620;
x_566 = x_601;
x_567 = x_602;
x_568 = x_618;
x_569 = x_605;
x_570 = x_606;
x_571 = x_607;
x_572 = x_608;
x_573 = x_609;
x_574 = x_610;
x_575 = x_611;
x_576 = x_612;
x_577 = x_613;
x_578 = x_621;
x_579 = x_623;
x_580 = x_626;
goto block_597;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_627 = lean_ctor_get(x_614, 0);
lean_inc(x_627);
lean_dec(x_614);
x_628 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_629 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_628);
x_630 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_612);
x_631 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_631, 0, x_612);
lean_ctor_set(x_631, 1, x_630);
x_632 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_612);
x_633 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_633, 0, x_612);
lean_ctor_set(x_633, 1, x_632);
x_634 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_612);
x_635 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_635, 0, x_612);
lean_ctor_set(x_635, 1, x_634);
x_636 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_612);
x_637 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_637, 0, x_612);
lean_ctor_set(x_637, 1, x_636);
lean_inc(x_612);
x_638 = l_Lean_Syntax_node5(x_612, x_629, x_631, x_633, x_635, x_627, x_637);
x_639 = l_Array_mkArray1___redArg(x_638);
x_561 = x_625;
x_562 = x_598;
x_563 = x_599;
x_564 = x_600;
x_565 = x_620;
x_566 = x_601;
x_567 = x_602;
x_568 = x_618;
x_569 = x_605;
x_570 = x_606;
x_571 = x_607;
x_572 = x_608;
x_573 = x_609;
x_574 = x_610;
x_575 = x_611;
x_576 = x_612;
x_577 = x_613;
x_578 = x_621;
x_579 = x_623;
x_580 = x_639;
goto block_597;
}
}
block_674:
{
lean_object* x_660; lean_object* x_661; 
lean_inc(x_654);
x_660 = l_Array_append(lean_box(0), x_654, x_659);
lean_dec(x_659);
lean_inc(x_653);
lean_inc(x_655);
x_661 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_661, 0, x_655);
lean_ctor_set(x_661, 1, x_653);
lean_ctor_set(x_661, 2, x_660);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_662; 
x_662 = l_Array_empty(lean_box(0));
x_598 = x_641;
x_599 = x_642;
x_600 = x_643;
x_601 = x_644;
x_602 = x_661;
x_603 = x_645;
x_604 = x_646;
x_605 = x_648;
x_606 = x_649;
x_607 = x_650;
x_608 = x_651;
x_609 = x_652;
x_610 = x_653;
x_611 = x_654;
x_612 = x_655;
x_613 = x_656;
x_614 = x_657;
x_615 = x_658;
x_616 = x_662;
goto block_640;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_663 = lean_ctor_get(x_647, 0);
lean_inc(x_663);
lean_dec(x_647);
x_664 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_644);
lean_inc(x_5);
lean_inc(x_4);
x_665 = l_Lean_Name_mkStr4(x_4, x_5, x_644, x_664);
x_666 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_655);
x_667 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_667, 0, x_655);
lean_ctor_set(x_667, 1, x_666);
lean_inc(x_654);
x_668 = l_Array_append(lean_box(0), x_654, x_663);
lean_dec(x_663);
lean_inc(x_653);
lean_inc(x_655);
x_669 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_669, 0, x_655);
lean_ctor_set(x_669, 1, x_653);
lean_ctor_set(x_669, 2, x_668);
x_670 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_655);
x_671 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_671, 0, x_655);
lean_ctor_set(x_671, 1, x_670);
lean_inc(x_655);
x_672 = l_Lean_Syntax_node3(x_655, x_665, x_667, x_669, x_671);
x_673 = l_Array_mkArray1___redArg(x_672);
x_598 = x_641;
x_599 = x_642;
x_600 = x_643;
x_601 = x_644;
x_602 = x_661;
x_603 = x_645;
x_604 = x_646;
x_605 = x_648;
x_606 = x_649;
x_607 = x_650;
x_608 = x_651;
x_609 = x_652;
x_610 = x_653;
x_611 = x_654;
x_612 = x_655;
x_613 = x_656;
x_614 = x_657;
x_615 = x_658;
x_616 = x_673;
goto block_640;
}
}
block_735:
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_695 = l_Array_append(lean_box(0), x_687, x_694);
lean_dec(x_694);
lean_inc(x_676);
lean_inc(x_688);
x_696 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_696, 0, x_688);
lean_ctor_set(x_696, 1, x_676);
lean_ctor_set(x_696, 2, x_695);
x_697 = lean_mk_string_unchecked("identPrec", 9, 9);
lean_inc(x_5);
lean_inc(x_4);
x_698 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_697);
x_699 = lean_mk_string_unchecked("lhs", 3, 3);
lean_inc(x_699);
x_700 = l_String_toSubstring_x27(x_699);
x_701 = l_Lean_Name_mkStr1(x_699);
lean_inc(x_681);
lean_inc(x_689);
x_702 = l_Lean_addMacroScope(x_689, x_701, x_681);
x_703 = lean_box(0);
lean_inc(x_688);
x_704 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_704, 0, x_688);
lean_ctor_set(x_704, 1, x_700);
lean_ctor_set(x_704, 2, x_702);
lean_ctor_set(x_704, 3, x_703);
lean_inc(x_680);
lean_inc(x_704);
lean_inc(x_698);
lean_inc(x_688);
x_705 = l_Lean_Syntax_node2(x_688, x_698, x_704, x_680);
x_706 = lean_mk_string_unchecked("rhs", 3, 3);
lean_inc(x_706);
x_707 = l_String_toSubstring_x27(x_706);
x_708 = l_Lean_Name_mkStr1(x_706);
x_709 = l_Lean_addMacroScope(x_689, x_708, x_681);
lean_inc(x_688);
x_710 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_710, 0, x_688);
lean_ctor_set(x_710, 1, x_707);
lean_ctor_set(x_710, 2, x_709);
lean_ctor_set(x_710, 3, x_703);
lean_inc(x_688);
x_711 = l_Lean_Syntax_node2(x_688, x_690, x_678, x_685);
lean_inc(x_676);
lean_inc(x_688);
x_712 = l_Lean_Syntax_node1(x_688, x_676, x_711);
lean_inc(x_710);
lean_inc(x_688);
x_713 = l_Lean_Syntax_node2(x_688, x_698, x_710, x_712);
lean_inc(x_676);
lean_inc(x_688);
x_714 = l_Lean_Syntax_node3(x_688, x_676, x_705, x_693, x_713);
x_715 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_688);
x_716 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_716, 0, x_688);
lean_ctor_set(x_716, 1, x_715);
x_717 = lean_mk_string_unchecked("app", 3, 3);
x_718 = l_Lean_Name_mkStr4(x_4, x_5, x_677, x_717);
lean_inc(x_688);
x_719 = l_Lean_Syntax_node2(x_688, x_676, x_704, x_710);
lean_inc(x_688);
x_720 = l_Lean_Syntax_node2(x_688, x_718, x_686, x_719);
x_721 = lean_unsigned_to_nat(10u);
x_722 = lean_mk_empty_array_with_capacity(x_721);
x_723 = lean_array_push(x_722, x_679);
x_724 = lean_array_push(x_723, x_675);
x_725 = lean_array_push(x_724, x_691);
x_726 = lean_array_push(x_725, x_692);
x_727 = lean_array_push(x_726, x_680);
x_728 = lean_array_push(x_727, x_682);
x_729 = lean_array_push(x_728, x_696);
x_730 = lean_array_push(x_729, x_714);
x_731 = lean_array_push(x_730, x_716);
x_732 = lean_array_push(x_731, x_720);
x_733 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_733, 0, x_688);
lean_ctor_set(x_733, 1, x_684);
lean_ctor_set(x_733, 2, x_732);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_683);
return x_734;
}
block_772:
{
lean_object* x_756; lean_object* x_757; 
lean_inc(x_748);
x_756 = l_Array_append(lean_box(0), x_748, x_755);
lean_dec(x_755);
lean_inc(x_737);
lean_inc(x_750);
x_757 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_757, 0, x_750);
lean_ctor_set(x_757, 1, x_737);
lean_ctor_set(x_757, 2, x_756);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_758; 
x_758 = l_Array_empty(lean_box(0));
x_675 = x_738;
x_676 = x_737;
x_677 = x_739;
x_678 = x_740;
x_679 = x_741;
x_680 = x_742;
x_681 = x_743;
x_682 = x_757;
x_683 = x_744;
x_684 = x_745;
x_685 = x_746;
x_686 = x_747;
x_687 = x_748;
x_688 = x_750;
x_689 = x_749;
x_690 = x_751;
x_691 = x_752;
x_692 = x_754;
x_693 = x_753;
x_694 = x_758;
goto block_735;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_759 = lean_ctor_get(x_736, 0);
lean_inc(x_759);
lean_dec(x_736);
x_760 = lean_mk_string_unchecked("namedPrio", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_761 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_760);
x_762 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_750);
x_763 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_763, 0, x_750);
lean_ctor_set(x_763, 1, x_762);
x_764 = lean_mk_string_unchecked("priority", 8, 8);
lean_inc(x_750);
x_765 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_765, 0, x_750);
lean_ctor_set(x_765, 1, x_764);
x_766 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_750);
x_767 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_767, 0, x_750);
lean_ctor_set(x_767, 1, x_766);
x_768 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_750);
x_769 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_769, 0, x_750);
lean_ctor_set(x_769, 1, x_768);
lean_inc(x_750);
x_770 = l_Lean_Syntax_node5(x_750, x_761, x_763, x_765, x_767, x_759, x_769);
x_771 = l_Array_mkArray1___redArg(x_770);
x_675 = x_738;
x_676 = x_737;
x_677 = x_739;
x_678 = x_740;
x_679 = x_741;
x_680 = x_742;
x_681 = x_743;
x_682 = x_757;
x_683 = x_744;
x_684 = x_745;
x_685 = x_746;
x_686 = x_747;
x_687 = x_748;
x_688 = x_750;
x_689 = x_749;
x_690 = x_751;
x_691 = x_752;
x_692 = x_754;
x_693 = x_753;
x_694 = x_771;
goto block_735;
}
}
block_815:
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_inc(x_785);
x_792 = l_Array_append(lean_box(0), x_785, x_791);
lean_dec(x_791);
lean_inc(x_774);
lean_inc(x_787);
x_793 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_793, 0, x_787);
lean_ctor_set(x_793, 1, x_774);
lean_ctor_set(x_793, 2, x_792);
lean_inc(x_785);
lean_inc(x_774);
lean_inc(x_787);
x_794 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_794, 0, x_787);
lean_ctor_set(x_794, 1, x_774);
lean_ctor_set(x_794, 2, x_785);
lean_inc(x_787);
x_795 = l_Lean_Syntax_node1(x_787, x_777, x_794);
lean_inc(x_787);
x_796 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_796, 0, x_787);
lean_ctor_set(x_796, 1, x_776);
x_797 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_787);
x_798 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_798, 0, x_787);
lean_ctor_set(x_798, 1, x_797);
lean_inc(x_798);
lean_inc(x_788);
lean_inc(x_787);
x_799 = l_Lean_Syntax_node2(x_787, x_788, x_798, x_779);
lean_inc(x_774);
lean_inc(x_787);
x_800 = l_Lean_Syntax_node1(x_787, x_774, x_799);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_801; 
x_801 = l_Array_empty(lean_box(0));
x_736 = x_773;
x_737 = x_774;
x_738 = x_793;
x_739 = x_775;
x_740 = x_798;
x_741 = x_778;
x_742 = x_800;
x_743 = x_780;
x_744 = x_781;
x_745 = x_782;
x_746 = x_784;
x_747 = x_783;
x_748 = x_785;
x_749 = x_786;
x_750 = x_787;
x_751 = x_788;
x_752 = x_795;
x_753 = x_789;
x_754 = x_796;
x_755 = x_801;
goto block_772;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_802 = lean_ctor_get(x_790, 0);
lean_inc(x_802);
lean_dec(x_790);
x_803 = lean_mk_string_unchecked("namedName", 9, 9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_804 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_803);
x_805 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_787);
x_806 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_806, 0, x_787);
lean_ctor_set(x_806, 1, x_805);
x_807 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_787);
x_808 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_808, 0, x_787);
lean_ctor_set(x_808, 1, x_807);
x_809 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_787);
x_810 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_810, 0, x_787);
lean_ctor_set(x_810, 1, x_809);
x_811 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_787);
x_812 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_812, 0, x_787);
lean_ctor_set(x_812, 1, x_811);
lean_inc(x_787);
x_813 = l_Lean_Syntax_node5(x_787, x_804, x_806, x_808, x_810, x_802, x_812);
x_814 = l_Array_mkArray1___redArg(x_813);
x_736 = x_773;
x_737 = x_774;
x_738 = x_793;
x_739 = x_775;
x_740 = x_798;
x_741 = x_778;
x_742 = x_800;
x_743 = x_780;
x_744 = x_781;
x_745 = x_782;
x_746 = x_784;
x_747 = x_783;
x_748 = x_785;
x_749 = x_786;
x_750 = x_787;
x_751 = x_788;
x_752 = x_795;
x_753 = x_789;
x_754 = x_796;
x_755 = x_814;
goto block_772;
}
}
block_849:
{
lean_object* x_835; lean_object* x_836; 
lean_inc(x_828);
x_835 = l_Array_append(lean_box(0), x_828, x_834);
lean_dec(x_834);
lean_inc(x_817);
lean_inc(x_830);
x_836 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_836, 0, x_830);
lean_ctor_set(x_836, 1, x_817);
lean_ctor_set(x_836, 2, x_835);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_837; 
x_837 = l_Array_empty(lean_box(0));
x_773 = x_816;
x_774 = x_817;
x_775 = x_818;
x_776 = x_819;
x_777 = x_820;
x_778 = x_836;
x_779 = x_821;
x_780 = x_823;
x_781 = x_824;
x_782 = x_825;
x_783 = x_826;
x_784 = x_827;
x_785 = x_828;
x_786 = x_829;
x_787 = x_830;
x_788 = x_831;
x_789 = x_832;
x_790 = x_833;
x_791 = x_837;
goto block_815;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_838 = lean_ctor_get(x_822, 0);
lean_inc(x_838);
lean_dec(x_822);
x_839 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_818);
lean_inc(x_5);
lean_inc(x_4);
x_840 = l_Lean_Name_mkStr4(x_4, x_5, x_818, x_839);
x_841 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_830);
x_842 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_842, 0, x_830);
lean_ctor_set(x_842, 1, x_841);
lean_inc(x_828);
x_843 = l_Array_append(lean_box(0), x_828, x_838);
lean_dec(x_838);
lean_inc(x_817);
lean_inc(x_830);
x_844 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_844, 0, x_830);
lean_ctor_set(x_844, 1, x_817);
lean_ctor_set(x_844, 2, x_843);
x_845 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_830);
x_846 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_846, 0, x_830);
lean_ctor_set(x_846, 1, x_845);
lean_inc(x_830);
x_847 = l_Lean_Syntax_node3(x_830, x_840, x_842, x_844, x_846);
x_848 = l_Array_mkArray1___redArg(x_847);
x_773 = x_816;
x_774 = x_817;
x_775 = x_818;
x_776 = x_819;
x_777 = x_820;
x_778 = x_836;
x_779 = x_821;
x_780 = x_823;
x_781 = x_824;
x_782 = x_825;
x_783 = x_826;
x_784 = x_827;
x_785 = x_828;
x_786 = x_829;
x_787 = x_830;
x_788 = x_831;
x_789 = x_832;
x_790 = x_833;
x_791 = x_848;
goto block_815;
}
}
block_877:
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_861 = lean_unsigned_to_nat(7u);
x_862 = l_Lean_Syntax_getArg(x_1, x_861);
x_863 = lean_unsigned_to_nat(9u);
x_864 = l_Lean_Syntax_getArg(x_1, x_863);
lean_dec(x_1);
x_865 = lean_ctor_get(x_859, 5);
lean_inc(x_865);
x_866 = l_Lean_SourceInfo_fromRef(x_865, x_851);
lean_dec(x_865);
x_867 = lean_ctor_get(x_859, 2);
lean_inc(x_867);
x_868 = lean_ctor_get(x_859, 1);
lean_inc(x_868);
lean_dec(x_859);
x_869 = lean_mk_string_unchecked("notation", 8, 8);
lean_inc(x_869);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_870 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_869);
x_871 = lean_mk_string_unchecked("null", 4, 4);
x_872 = l_Lean_Name_mkStr1(x_871);
x_873 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_874; 
x_874 = l_Array_empty(lean_box(0));
x_133 = x_860;
x_134 = x_852;
x_135 = x_864;
x_136 = x_867;
x_137 = x_854;
x_138 = x_870;
x_139 = x_855;
x_140 = x_856;
x_141 = x_868;
x_142 = x_873;
x_143 = x_872;
x_144 = x_858;
x_145 = x_853;
x_146 = x_869;
x_147 = x_866;
x_148 = x_862;
x_149 = x_857;
x_150 = x_874;
goto block_165;
}
else
{
lean_object* x_875; lean_object* x_876; 
x_875 = lean_ctor_get(x_850, 0);
lean_inc(x_875);
lean_dec(x_850);
x_876 = l_Array_mkArray1___redArg(x_875);
x_133 = x_860;
x_134 = x_852;
x_135 = x_864;
x_136 = x_867;
x_137 = x_854;
x_138 = x_870;
x_139 = x_855;
x_140 = x_856;
x_141 = x_868;
x_142 = x_873;
x_143 = x_872;
x_144 = x_858;
x_145 = x_853;
x_146 = x_869;
x_147 = x_866;
x_148 = x_862;
x_149 = x_857;
x_150 = x_876;
goto block_165;
}
}
block_905:
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_889 = lean_unsigned_to_nat(7u);
x_890 = l_Lean_Syntax_getArg(x_1, x_889);
x_891 = lean_unsigned_to_nat(9u);
x_892 = l_Lean_Syntax_getArg(x_1, x_891);
lean_dec(x_1);
x_893 = lean_ctor_get(x_887, 5);
lean_inc(x_893);
x_894 = l_Lean_SourceInfo_fromRef(x_893, x_884);
lean_dec(x_893);
x_895 = lean_ctor_get(x_887, 2);
lean_inc(x_895);
x_896 = lean_ctor_get(x_887, 1);
lean_inc(x_896);
lean_dec(x_887);
x_897 = lean_mk_string_unchecked("notation", 8, 8);
lean_inc(x_897);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_898 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_897);
x_899 = lean_mk_string_unchecked("null", 4, 4);
x_900 = l_Lean_Name_mkStr1(x_899);
x_901 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_902; 
x_902 = l_Array_empty(lean_box(0));
x_292 = x_878;
x_293 = x_900;
x_294 = x_881;
x_295 = x_890;
x_296 = x_883;
x_297 = x_886;
x_298 = x_885;
x_299 = x_901;
x_300 = x_898;
x_301 = x_897;
x_302 = x_888;
x_303 = x_892;
x_304 = x_880;
x_305 = x_882;
x_306 = x_895;
x_307 = x_896;
x_308 = x_894;
x_309 = x_902;
goto block_324;
}
else
{
lean_object* x_903; lean_object* x_904; 
x_903 = lean_ctor_get(x_879, 0);
lean_inc(x_903);
lean_dec(x_879);
x_904 = l_Array_mkArray1___redArg(x_903);
x_292 = x_878;
x_293 = x_900;
x_294 = x_881;
x_295 = x_890;
x_296 = x_883;
x_297 = x_886;
x_298 = x_885;
x_299 = x_901;
x_300 = x_898;
x_301 = x_897;
x_302 = x_888;
x_303 = x_892;
x_304 = x_880;
x_305 = x_882;
x_306 = x_895;
x_307 = x_896;
x_308 = x_894;
x_309 = x_904;
goto block_324;
}
}
block_945:
{
lean_object* x_918; 
lean_inc(x_914);
x_918 = l_Lean_evalPrec(x_914, x_916, x_917);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec(x_918);
x_921 = lean_unsigned_to_nat(7u);
x_922 = lean_unsigned_to_nat(9u);
x_923 = l_Lean_Syntax_getArg(x_1, x_921);
x_924 = l_Lean_Syntax_getArg(x_1, x_922);
lean_dec(x_1);
x_925 = lean_nat_add(x_919, x_913);
lean_dec(x_919);
x_926 = l___private_Init_Data_Repr_0__Nat_reprFast(x_925);
x_927 = lean_box(2);
x_928 = l_Lean_Syntax_mkNumLit(x_926, x_927);
x_929 = lean_ctor_get(x_916, 5);
lean_inc(x_929);
x_930 = l_Lean_SourceInfo_fromRef(x_929, x_911);
lean_dec(x_929);
x_931 = lean_ctor_get(x_916, 2);
lean_inc(x_931);
x_932 = lean_ctor_get(x_916, 1);
lean_inc(x_932);
lean_dec(x_916);
x_933 = lean_mk_string_unchecked("notation", 8, 8);
lean_inc(x_933);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_934 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_933);
x_935 = lean_mk_string_unchecked("null", 4, 4);
x_936 = l_Lean_Name_mkStr1(x_935);
x_937 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_938; 
x_938 = l_Array_empty(lean_box(0));
x_466 = x_906;
x_467 = x_915;
x_468 = x_923;
x_469 = x_908;
x_470 = x_909;
x_471 = x_910;
x_472 = x_937;
x_473 = x_912;
x_474 = x_924;
x_475 = x_932;
x_476 = x_928;
x_477 = x_931;
x_478 = x_934;
x_479 = x_936;
x_480 = x_920;
x_481 = x_930;
x_482 = x_933;
x_483 = x_914;
x_484 = x_938;
goto block_499;
}
else
{
lean_object* x_939; lean_object* x_940; 
x_939 = lean_ctor_get(x_907, 0);
lean_inc(x_939);
lean_dec(x_907);
x_940 = l_Array_mkArray1___redArg(x_939);
x_466 = x_906;
x_467 = x_915;
x_468 = x_923;
x_469 = x_908;
x_470 = x_909;
x_471 = x_910;
x_472 = x_937;
x_473 = x_912;
x_474 = x_924;
x_475 = x_932;
x_476 = x_928;
x_477 = x_931;
x_478 = x_934;
x_479 = x_936;
x_480 = x_920;
x_481 = x_930;
x_482 = x_933;
x_483 = x_914;
x_484 = x_940;
goto block_499;
}
}
else
{
uint8_t x_941; 
lean_dec(x_916);
lean_dec(x_915);
lean_dec(x_914);
lean_dec(x_912);
lean_dec(x_910);
lean_dec(x_909);
lean_dec(x_908);
lean_dec(x_907);
lean_dec(x_906);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_941 = !lean_is_exclusive(x_918);
if (x_941 == 0)
{
return x_918;
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_942 = lean_ctor_get(x_918, 0);
x_943 = lean_ctor_get(x_918, 1);
lean_inc(x_943);
lean_inc(x_942);
lean_dec(x_918);
x_944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_944, 0, x_942);
lean_ctor_set(x_944, 1, x_943);
return x_944;
}
}
}
block_985:
{
lean_object* x_958; 
lean_inc(x_949);
x_958 = l_Lean_evalPrec(x_949, x_956, x_957);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = lean_unsigned_to_nat(7u);
x_962 = lean_unsigned_to_nat(9u);
x_963 = l_Lean_Syntax_getArg(x_1, x_961);
x_964 = l_Lean_Syntax_getArg(x_1, x_962);
lean_dec(x_1);
x_965 = lean_nat_add(x_959, x_952);
lean_dec(x_959);
x_966 = l___private_Init_Data_Repr_0__Nat_reprFast(x_965);
x_967 = lean_box(2);
x_968 = l_Lean_Syntax_mkNumLit(x_966, x_967);
x_969 = lean_ctor_get(x_956, 5);
lean_inc(x_969);
x_970 = l_Lean_SourceInfo_fromRef(x_969, x_954);
lean_dec(x_969);
x_971 = lean_ctor_get(x_956, 2);
lean_inc(x_971);
x_972 = lean_ctor_get(x_956, 1);
lean_inc(x_972);
lean_dec(x_956);
x_973 = lean_mk_string_unchecked("notation", 8, 8);
lean_inc(x_973);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_974 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_973);
x_975 = lean_mk_string_unchecked("null", 4, 4);
x_976 = l_Lean_Name_mkStr1(x_975);
x_977 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_978; 
x_978 = l_Array_empty(lean_box(0));
x_641 = x_974;
x_642 = x_955;
x_643 = x_963;
x_644 = x_947;
x_645 = x_949;
x_646 = x_950;
x_647 = x_951;
x_648 = x_953;
x_649 = x_964;
x_650 = x_968;
x_651 = x_960;
x_652 = x_972;
x_653 = x_976;
x_654 = x_977;
x_655 = x_970;
x_656 = x_971;
x_657 = x_948;
x_658 = x_973;
x_659 = x_978;
goto block_674;
}
else
{
lean_object* x_979; lean_object* x_980; 
x_979 = lean_ctor_get(x_946, 0);
lean_inc(x_979);
lean_dec(x_946);
x_980 = l_Array_mkArray1___redArg(x_979);
x_641 = x_974;
x_642 = x_955;
x_643 = x_963;
x_644 = x_947;
x_645 = x_949;
x_646 = x_950;
x_647 = x_951;
x_648 = x_953;
x_649 = x_964;
x_650 = x_968;
x_651 = x_960;
x_652 = x_972;
x_653 = x_976;
x_654 = x_977;
x_655 = x_970;
x_656 = x_971;
x_657 = x_948;
x_658 = x_973;
x_659 = x_980;
goto block_674;
}
}
else
{
uint8_t x_981; 
lean_dec(x_956);
lean_dec(x_955);
lean_dec(x_953);
lean_dec(x_951);
lean_dec(x_950);
lean_dec(x_949);
lean_dec(x_948);
lean_dec(x_947);
lean_dec(x_946);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_981 = !lean_is_exclusive(x_958);
if (x_981 == 0)
{
return x_958;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_982 = lean_ctor_get(x_958, 0);
x_983 = lean_ctor_get(x_958, 1);
lean_inc(x_983);
lean_inc(x_982);
lean_dec(x_958);
x_984 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_984, 0, x_982);
lean_ctor_set(x_984, 1, x_983);
return x_984;
}
}
}
block_1026:
{
lean_object* x_997; 
lean_inc(x_989);
x_997 = l_Lean_evalPrec(x_989, x_995, x_996);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
lean_dec(x_997);
x_1000 = lean_unsigned_to_nat(7u);
x_1001 = lean_unsigned_to_nat(9u);
x_1002 = l_Lean_Syntax_getArg(x_1, x_1000);
x_1003 = l_Lean_Syntax_getArg(x_1, x_1001);
lean_dec(x_1);
x_1004 = lean_nat_add(x_998, x_992);
lean_dec(x_998);
x_1005 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1004);
x_1006 = lean_box(2);
x_1007 = l_Lean_Syntax_mkNumLit(x_1005, x_1006);
x_1008 = lean_ctor_get(x_995, 5);
lean_inc(x_1008);
x_1009 = lean_box(0);
x_1010 = lean_unbox(x_1009);
x_1011 = l_Lean_SourceInfo_fromRef(x_1008, x_1010);
lean_dec(x_1008);
x_1012 = lean_ctor_get(x_995, 2);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_995, 1);
lean_inc(x_1013);
lean_dec(x_995);
x_1014 = lean_mk_string_unchecked("notation", 8, 8);
lean_inc(x_1014);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1015 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_1014);
x_1016 = lean_mk_string_unchecked("null", 4, 4);
x_1017 = l_Lean_Name_mkStr1(x_1016);
x_1018 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_1019; 
x_1019 = l_Array_empty(lean_box(0));
x_816 = x_994;
x_817 = x_1017;
x_818 = x_987;
x_819 = x_1014;
x_820 = x_988;
x_821 = x_989;
x_822 = x_991;
x_823 = x_1012;
x_824 = x_999;
x_825 = x_1015;
x_826 = x_1003;
x_827 = x_1007;
x_828 = x_1018;
x_829 = x_1013;
x_830 = x_1011;
x_831 = x_990;
x_832 = x_1002;
x_833 = x_993;
x_834 = x_1019;
goto block_849;
}
else
{
lean_object* x_1020; lean_object* x_1021; 
x_1020 = lean_ctor_get(x_986, 0);
lean_inc(x_1020);
lean_dec(x_986);
x_1021 = l_Array_mkArray1___redArg(x_1020);
x_816 = x_994;
x_817 = x_1017;
x_818 = x_987;
x_819 = x_1014;
x_820 = x_988;
x_821 = x_989;
x_822 = x_991;
x_823 = x_1012;
x_824 = x_999;
x_825 = x_1015;
x_826 = x_1003;
x_827 = x_1007;
x_828 = x_1018;
x_829 = x_1013;
x_830 = x_1011;
x_831 = x_990;
x_832 = x_1002;
x_833 = x_993;
x_834 = x_1021;
goto block_849;
}
}
else
{
uint8_t x_1022; 
lean_dec(x_995);
lean_dec(x_994);
lean_dec(x_993);
lean_dec(x_991);
lean_dec(x_990);
lean_dec(x_989);
lean_dec(x_988);
lean_dec(x_987);
lean_dec(x_986);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1022 = !lean_is_exclusive(x_997);
if (x_1022 == 0)
{
return x_997;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_997, 0);
x_1024 = lean_ctor_get(x_997, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_997);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandMixfix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMixfix___lam__0), 3, 0);
x_5 = l_Lean_Elab_Command_expandMixfix_withAttrKindGlobal(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMixfix__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("mixfix", 6, 6);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("expandMixfix", 12, 12);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandMixfix), 3, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Elab", 4, 4);
x_4 = lean_mk_string_unchecked("Command", 7, 7);
x_5 = lean_mk_string_unchecked("expandMixfix", 12, 12);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(11u);
x_8 = lean_unsigned_to_nat(44u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(34u);
x_11 = lean_unsigned_to_nat(36u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_unsigned_to_nat(48u);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(60u);
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
lean_object* initialize_Lean_Elab_Attributes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Mixfix(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMixfix__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Command_expandMixfix_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
