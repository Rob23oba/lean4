// Lean compiler output
// Module: Lean.Data.Json.Printer
// Imports: Lean.Data.Format Lean.Data.Json.Basic Init.Data.List.Impl
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_render_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_compress_go_spec__0(size_t, size_t, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lean_Json_escape_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Json_compress_go_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Json_compress_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_renderString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instToString;
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_compress_go(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_escape___boxed(lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lean_Json_escape_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_instToFormat;
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_render_spec__1(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_render_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_compress_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_uint8_of_nat(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_uint8_of_nat(x_3);
x_5 = lean_unsigned_to_nat(256u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_box(x_2);
x_8 = lean_array_push(x_6, x_7);
x_9 = lean_box(x_2);
x_10 = lean_array_push(x_8, x_9);
x_11 = lean_box(x_2);
x_12 = lean_array_push(x_10, x_11);
x_13 = lean_box(x_2);
x_14 = lean_array_push(x_12, x_13);
x_15 = lean_box(x_2);
x_16 = lean_array_push(x_14, x_15);
x_17 = lean_box(x_2);
x_18 = lean_array_push(x_16, x_17);
x_19 = lean_box(x_2);
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_box(x_2);
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_box(x_2);
x_24 = lean_array_push(x_22, x_23);
x_25 = lean_box(x_2);
x_26 = lean_array_push(x_24, x_25);
x_27 = lean_box(x_2);
x_28 = lean_array_push(x_26, x_27);
x_29 = lean_box(x_2);
x_30 = lean_array_push(x_28, x_29);
x_31 = lean_box(x_2);
x_32 = lean_array_push(x_30, x_31);
x_33 = lean_box(x_2);
x_34 = lean_array_push(x_32, x_33);
x_35 = lean_box(x_2);
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_box(x_2);
x_38 = lean_array_push(x_36, x_37);
x_39 = lean_box(x_2);
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_box(x_2);
x_42 = lean_array_push(x_40, x_41);
x_43 = lean_box(x_2);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_box(x_2);
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_box(x_2);
x_48 = lean_array_push(x_46, x_47);
x_49 = lean_box(x_2);
x_50 = lean_array_push(x_48, x_49);
x_51 = lean_box(x_2);
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_box(x_2);
x_54 = lean_array_push(x_52, x_53);
x_55 = lean_box(x_2);
x_56 = lean_array_push(x_54, x_55);
x_57 = lean_box(x_2);
x_58 = lean_array_push(x_56, x_57);
x_59 = lean_box(x_2);
x_60 = lean_array_push(x_58, x_59);
x_61 = lean_box(x_2);
x_62 = lean_array_push(x_60, x_61);
x_63 = lean_box(x_2);
x_64 = lean_array_push(x_62, x_63);
x_65 = lean_box(x_2);
x_66 = lean_array_push(x_64, x_65);
x_67 = lean_box(x_2);
x_68 = lean_array_push(x_66, x_67);
x_69 = lean_box(x_2);
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_box(x_4);
x_72 = lean_array_push(x_70, x_71);
x_73 = lean_box(x_4);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_box(x_2);
x_76 = lean_array_push(x_74, x_75);
x_77 = lean_box(x_4);
x_78 = lean_array_push(x_76, x_77);
x_79 = lean_box(x_4);
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_box(x_4);
x_82 = lean_array_push(x_80, x_81);
x_83 = lean_box(x_4);
x_84 = lean_array_push(x_82, x_83);
x_85 = lean_box(x_4);
x_86 = lean_array_push(x_84, x_85);
x_87 = lean_box(x_4);
x_88 = lean_array_push(x_86, x_87);
x_89 = lean_box(x_4);
x_90 = lean_array_push(x_88, x_89);
x_91 = lean_box(x_4);
x_92 = lean_array_push(x_90, x_91);
x_93 = lean_box(x_4);
x_94 = lean_array_push(x_92, x_93);
x_95 = lean_box(x_4);
x_96 = lean_array_push(x_94, x_95);
x_97 = lean_box(x_4);
x_98 = lean_array_push(x_96, x_97);
x_99 = lean_box(x_4);
x_100 = lean_array_push(x_98, x_99);
x_101 = lean_box(x_2);
x_102 = lean_array_push(x_100, x_101);
x_103 = lean_box(x_4);
x_104 = lean_array_push(x_102, x_103);
x_105 = lean_box(x_4);
x_106 = lean_array_push(x_104, x_105);
x_107 = lean_box(x_4);
x_108 = lean_array_push(x_106, x_107);
x_109 = lean_box(x_4);
x_110 = lean_array_push(x_108, x_109);
x_111 = lean_box(x_4);
x_112 = lean_array_push(x_110, x_111);
x_113 = lean_box(x_4);
x_114 = lean_array_push(x_112, x_113);
x_115 = lean_box(x_4);
x_116 = lean_array_push(x_114, x_115);
x_117 = lean_box(x_4);
x_118 = lean_array_push(x_116, x_117);
x_119 = lean_box(x_4);
x_120 = lean_array_push(x_118, x_119);
x_121 = lean_box(x_4);
x_122 = lean_array_push(x_120, x_121);
x_123 = lean_box(x_4);
x_124 = lean_array_push(x_122, x_123);
x_125 = lean_box(x_4);
x_126 = lean_array_push(x_124, x_125);
x_127 = lean_box(x_4);
x_128 = lean_array_push(x_126, x_127);
x_129 = lean_box(x_4);
x_130 = lean_array_push(x_128, x_129);
x_131 = lean_box(x_4);
x_132 = lean_array_push(x_130, x_131);
x_133 = lean_box(x_4);
x_134 = lean_array_push(x_132, x_133);
x_135 = lean_box(x_4);
x_136 = lean_array_push(x_134, x_135);
x_137 = lean_box(x_4);
x_138 = lean_array_push(x_136, x_137);
x_139 = lean_box(x_4);
x_140 = lean_array_push(x_138, x_139);
x_141 = lean_box(x_4);
x_142 = lean_array_push(x_140, x_141);
x_143 = lean_box(x_4);
x_144 = lean_array_push(x_142, x_143);
x_145 = lean_box(x_4);
x_146 = lean_array_push(x_144, x_145);
x_147 = lean_box(x_4);
x_148 = lean_array_push(x_146, x_147);
x_149 = lean_box(x_4);
x_150 = lean_array_push(x_148, x_149);
x_151 = lean_box(x_4);
x_152 = lean_array_push(x_150, x_151);
x_153 = lean_box(x_4);
x_154 = lean_array_push(x_152, x_153);
x_155 = lean_box(x_4);
x_156 = lean_array_push(x_154, x_155);
x_157 = lean_box(x_4);
x_158 = lean_array_push(x_156, x_157);
x_159 = lean_box(x_4);
x_160 = lean_array_push(x_158, x_159);
x_161 = lean_box(x_4);
x_162 = lean_array_push(x_160, x_161);
x_163 = lean_box(x_4);
x_164 = lean_array_push(x_162, x_163);
x_165 = lean_box(x_4);
x_166 = lean_array_push(x_164, x_165);
x_167 = lean_box(x_4);
x_168 = lean_array_push(x_166, x_167);
x_169 = lean_box(x_4);
x_170 = lean_array_push(x_168, x_169);
x_171 = lean_box(x_4);
x_172 = lean_array_push(x_170, x_171);
x_173 = lean_box(x_4);
x_174 = lean_array_push(x_172, x_173);
x_175 = lean_box(x_4);
x_176 = lean_array_push(x_174, x_175);
x_177 = lean_box(x_4);
x_178 = lean_array_push(x_176, x_177);
x_179 = lean_box(x_4);
x_180 = lean_array_push(x_178, x_179);
x_181 = lean_box(x_4);
x_182 = lean_array_push(x_180, x_181);
x_183 = lean_box(x_4);
x_184 = lean_array_push(x_182, x_183);
x_185 = lean_box(x_4);
x_186 = lean_array_push(x_184, x_185);
x_187 = lean_box(x_4);
x_188 = lean_array_push(x_186, x_187);
x_189 = lean_box(x_4);
x_190 = lean_array_push(x_188, x_189);
x_191 = lean_box(x_2);
x_192 = lean_array_push(x_190, x_191);
x_193 = lean_box(x_4);
x_194 = lean_array_push(x_192, x_193);
x_195 = lean_box(x_4);
x_196 = lean_array_push(x_194, x_195);
x_197 = lean_box(x_4);
x_198 = lean_array_push(x_196, x_197);
x_199 = lean_box(x_4);
x_200 = lean_array_push(x_198, x_199);
x_201 = lean_box(x_4);
x_202 = lean_array_push(x_200, x_201);
x_203 = lean_box(x_4);
x_204 = lean_array_push(x_202, x_203);
x_205 = lean_box(x_4);
x_206 = lean_array_push(x_204, x_205);
x_207 = lean_box(x_4);
x_208 = lean_array_push(x_206, x_207);
x_209 = lean_box(x_4);
x_210 = lean_array_push(x_208, x_209);
x_211 = lean_box(x_4);
x_212 = lean_array_push(x_210, x_211);
x_213 = lean_box(x_4);
x_214 = lean_array_push(x_212, x_213);
x_215 = lean_box(x_4);
x_216 = lean_array_push(x_214, x_215);
x_217 = lean_box(x_4);
x_218 = lean_array_push(x_216, x_217);
x_219 = lean_box(x_4);
x_220 = lean_array_push(x_218, x_219);
x_221 = lean_box(x_4);
x_222 = lean_array_push(x_220, x_221);
x_223 = lean_box(x_4);
x_224 = lean_array_push(x_222, x_223);
x_225 = lean_box(x_4);
x_226 = lean_array_push(x_224, x_225);
x_227 = lean_box(x_4);
x_228 = lean_array_push(x_226, x_227);
x_229 = lean_box(x_4);
x_230 = lean_array_push(x_228, x_229);
x_231 = lean_box(x_4);
x_232 = lean_array_push(x_230, x_231);
x_233 = lean_box(x_4);
x_234 = lean_array_push(x_232, x_233);
x_235 = lean_box(x_4);
x_236 = lean_array_push(x_234, x_235);
x_237 = lean_box(x_4);
x_238 = lean_array_push(x_236, x_237);
x_239 = lean_box(x_4);
x_240 = lean_array_push(x_238, x_239);
x_241 = lean_box(x_4);
x_242 = lean_array_push(x_240, x_241);
x_243 = lean_box(x_4);
x_244 = lean_array_push(x_242, x_243);
x_245 = lean_box(x_4);
x_246 = lean_array_push(x_244, x_245);
x_247 = lean_box(x_4);
x_248 = lean_array_push(x_246, x_247);
x_249 = lean_box(x_4);
x_250 = lean_array_push(x_248, x_249);
x_251 = lean_box(x_4);
x_252 = lean_array_push(x_250, x_251);
x_253 = lean_box(x_4);
x_254 = lean_array_push(x_252, x_253);
x_255 = lean_box(x_4);
x_256 = lean_array_push(x_254, x_255);
x_257 = lean_box(x_4);
x_258 = lean_array_push(x_256, x_257);
x_259 = lean_box(x_4);
x_260 = lean_array_push(x_258, x_259);
x_261 = lean_box(x_4);
x_262 = lean_array_push(x_260, x_261);
x_263 = lean_box(x_2);
x_264 = lean_array_push(x_262, x_263);
x_265 = lean_box(x_2);
x_266 = lean_array_push(x_264, x_265);
x_267 = lean_box(x_2);
x_268 = lean_array_push(x_266, x_267);
x_269 = lean_box(x_2);
x_270 = lean_array_push(x_268, x_269);
x_271 = lean_box(x_2);
x_272 = lean_array_push(x_270, x_271);
x_273 = lean_box(x_2);
x_274 = lean_array_push(x_272, x_273);
x_275 = lean_box(x_2);
x_276 = lean_array_push(x_274, x_275);
x_277 = lean_box(x_2);
x_278 = lean_array_push(x_276, x_277);
x_279 = lean_box(x_2);
x_280 = lean_array_push(x_278, x_279);
x_281 = lean_box(x_2);
x_282 = lean_array_push(x_280, x_281);
x_283 = lean_box(x_2);
x_284 = lean_array_push(x_282, x_283);
x_285 = lean_box(x_2);
x_286 = lean_array_push(x_284, x_285);
x_287 = lean_box(x_2);
x_288 = lean_array_push(x_286, x_287);
x_289 = lean_box(x_2);
x_290 = lean_array_push(x_288, x_289);
x_291 = lean_box(x_2);
x_292 = lean_array_push(x_290, x_291);
x_293 = lean_box(x_2);
x_294 = lean_array_push(x_292, x_293);
x_295 = lean_box(x_2);
x_296 = lean_array_push(x_294, x_295);
x_297 = lean_box(x_2);
x_298 = lean_array_push(x_296, x_297);
x_299 = lean_box(x_2);
x_300 = lean_array_push(x_298, x_299);
x_301 = lean_box(x_2);
x_302 = lean_array_push(x_300, x_301);
x_303 = lean_box(x_2);
x_304 = lean_array_push(x_302, x_303);
x_305 = lean_box(x_2);
x_306 = lean_array_push(x_304, x_305);
x_307 = lean_box(x_2);
x_308 = lean_array_push(x_306, x_307);
x_309 = lean_box(x_2);
x_310 = lean_array_push(x_308, x_309);
x_311 = lean_box(x_2);
x_312 = lean_array_push(x_310, x_311);
x_313 = lean_box(x_2);
x_314 = lean_array_push(x_312, x_313);
x_315 = lean_box(x_2);
x_316 = lean_array_push(x_314, x_315);
x_317 = lean_box(x_2);
x_318 = lean_array_push(x_316, x_317);
x_319 = lean_box(x_2);
x_320 = lean_array_push(x_318, x_319);
x_321 = lean_box(x_2);
x_322 = lean_array_push(x_320, x_321);
x_323 = lean_box(x_2);
x_324 = lean_array_push(x_322, x_323);
x_325 = lean_box(x_2);
x_326 = lean_array_push(x_324, x_325);
x_327 = lean_box(x_2);
x_328 = lean_array_push(x_326, x_327);
x_329 = lean_box(x_2);
x_330 = lean_array_push(x_328, x_329);
x_331 = lean_box(x_2);
x_332 = lean_array_push(x_330, x_331);
x_333 = lean_box(x_2);
x_334 = lean_array_push(x_332, x_333);
x_335 = lean_box(x_2);
x_336 = lean_array_push(x_334, x_335);
x_337 = lean_box(x_2);
x_338 = lean_array_push(x_336, x_337);
x_339 = lean_box(x_2);
x_340 = lean_array_push(x_338, x_339);
x_341 = lean_box(x_2);
x_342 = lean_array_push(x_340, x_341);
x_343 = lean_box(x_2);
x_344 = lean_array_push(x_342, x_343);
x_345 = lean_box(x_2);
x_346 = lean_array_push(x_344, x_345);
x_347 = lean_box(x_2);
x_348 = lean_array_push(x_346, x_347);
x_349 = lean_box(x_2);
x_350 = lean_array_push(x_348, x_349);
x_351 = lean_box(x_2);
x_352 = lean_array_push(x_350, x_351);
x_353 = lean_box(x_2);
x_354 = lean_array_push(x_352, x_353);
x_355 = lean_box(x_2);
x_356 = lean_array_push(x_354, x_355);
x_357 = lean_box(x_2);
x_358 = lean_array_push(x_356, x_357);
x_359 = lean_box(x_2);
x_360 = lean_array_push(x_358, x_359);
x_361 = lean_box(x_2);
x_362 = lean_array_push(x_360, x_361);
x_363 = lean_box(x_2);
x_364 = lean_array_push(x_362, x_363);
x_365 = lean_box(x_2);
x_366 = lean_array_push(x_364, x_365);
x_367 = lean_box(x_2);
x_368 = lean_array_push(x_366, x_367);
x_369 = lean_box(x_2);
x_370 = lean_array_push(x_368, x_369);
x_371 = lean_box(x_2);
x_372 = lean_array_push(x_370, x_371);
x_373 = lean_box(x_2);
x_374 = lean_array_push(x_372, x_373);
x_375 = lean_box(x_2);
x_376 = lean_array_push(x_374, x_375);
x_377 = lean_box(x_2);
x_378 = lean_array_push(x_376, x_377);
x_379 = lean_box(x_2);
x_380 = lean_array_push(x_378, x_379);
x_381 = lean_box(x_2);
x_382 = lean_array_push(x_380, x_381);
x_383 = lean_box(x_2);
x_384 = lean_array_push(x_382, x_383);
x_385 = lean_box(x_2);
x_386 = lean_array_push(x_384, x_385);
x_387 = lean_box(x_2);
x_388 = lean_array_push(x_386, x_387);
x_389 = lean_box(x_2);
x_390 = lean_array_push(x_388, x_389);
x_391 = lean_box(x_2);
x_392 = lean_array_push(x_390, x_391);
x_393 = lean_box(x_2);
x_394 = lean_array_push(x_392, x_393);
x_395 = lean_box(x_2);
x_396 = lean_array_push(x_394, x_395);
x_397 = lean_box(x_2);
x_398 = lean_array_push(x_396, x_397);
x_399 = lean_box(x_2);
x_400 = lean_array_push(x_398, x_399);
x_401 = lean_box(x_2);
x_402 = lean_array_push(x_400, x_401);
x_403 = lean_box(x_2);
x_404 = lean_array_push(x_402, x_403);
x_405 = lean_box(x_2);
x_406 = lean_array_push(x_404, x_405);
x_407 = lean_box(x_2);
x_408 = lean_array_push(x_406, x_407);
x_409 = lean_box(x_2);
x_410 = lean_array_push(x_408, x_409);
x_411 = lean_box(x_2);
x_412 = lean_array_push(x_410, x_411);
x_413 = lean_box(x_2);
x_414 = lean_array_push(x_412, x_413);
x_415 = lean_box(x_2);
x_416 = lean_array_push(x_414, x_415);
x_417 = lean_box(x_2);
x_418 = lean_array_push(x_416, x_417);
x_419 = lean_box(x_2);
x_420 = lean_array_push(x_418, x_419);
x_421 = lean_box(x_2);
x_422 = lean_array_push(x_420, x_421);
x_423 = lean_box(x_2);
x_424 = lean_array_push(x_422, x_423);
x_425 = lean_box(x_2);
x_426 = lean_array_push(x_424, x_425);
x_427 = lean_box(x_2);
x_428 = lean_array_push(x_426, x_427);
x_429 = lean_box(x_2);
x_430 = lean_array_push(x_428, x_429);
x_431 = lean_box(x_2);
x_432 = lean_array_push(x_430, x_431);
x_433 = lean_box(x_2);
x_434 = lean_array_push(x_432, x_433);
x_435 = lean_box(x_2);
x_436 = lean_array_push(x_434, x_435);
x_437 = lean_box(x_2);
x_438 = lean_array_push(x_436, x_437);
x_439 = lean_box(x_2);
x_440 = lean_array_push(x_438, x_439);
x_441 = lean_box(x_2);
x_442 = lean_array_push(x_440, x_441);
x_443 = lean_box(x_2);
x_444 = lean_array_push(x_442, x_443);
x_445 = lean_box(x_2);
x_446 = lean_array_push(x_444, x_445);
x_447 = lean_box(x_2);
x_448 = lean_array_push(x_446, x_447);
x_449 = lean_box(x_2);
x_450 = lean_array_push(x_448, x_449);
x_451 = lean_box(x_2);
x_452 = lean_array_push(x_450, x_451);
x_453 = lean_box(x_2);
x_454 = lean_array_push(x_452, x_453);
x_455 = lean_box(x_2);
x_456 = lean_array_push(x_454, x_455);
x_457 = lean_box(x_2);
x_458 = lean_array_push(x_456, x_457);
x_459 = lean_box(x_2);
x_460 = lean_array_push(x_458, x_459);
x_461 = lean_box(x_2);
x_462 = lean_array_push(x_460, x_461);
x_463 = lean_box(x_2);
x_464 = lean_array_push(x_462, x_463);
x_465 = lean_box(x_2);
x_466 = lean_array_push(x_464, x_465);
x_467 = lean_box(x_2);
x_468 = lean_array_push(x_466, x_467);
x_469 = lean_box(x_2);
x_470 = lean_array_push(x_468, x_469);
x_471 = lean_box(x_2);
x_472 = lean_array_push(x_470, x_471);
x_473 = lean_box(x_2);
x_474 = lean_array_push(x_472, x_473);
x_475 = lean_box(x_2);
x_476 = lean_array_push(x_474, x_475);
x_477 = lean_box(x_2);
x_478 = lean_array_push(x_476, x_477);
x_479 = lean_box(x_2);
x_480 = lean_array_push(x_478, x_479);
x_481 = lean_box(x_2);
x_482 = lean_array_push(x_480, x_481);
x_483 = lean_box(x_2);
x_484 = lean_array_push(x_482, x_483);
x_485 = lean_box(x_2);
x_486 = lean_array_push(x_484, x_485);
x_487 = lean_box(x_2);
x_488 = lean_array_push(x_486, x_487);
x_489 = lean_box(x_2);
x_490 = lean_array_push(x_488, x_489);
x_491 = lean_box(x_2);
x_492 = lean_array_push(x_490, x_491);
x_493 = lean_box(x_2);
x_494 = lean_array_push(x_492, x_493);
x_495 = lean_box(x_2);
x_496 = lean_array_push(x_494, x_495);
x_497 = lean_box(x_2);
x_498 = lean_array_push(x_496, x_497);
x_499 = lean_box(x_2);
x_500 = lean_array_push(x_498, x_499);
x_501 = lean_box(x_2);
x_502 = lean_array_push(x_500, x_501);
x_503 = lean_box(x_2);
x_504 = lean_array_push(x_502, x_503);
x_505 = lean_box(x_2);
x_506 = lean_array_push(x_504, x_505);
x_507 = lean_box(x_2);
x_508 = lean_array_push(x_506, x_507);
x_509 = lean_box(x_2);
x_510 = lean_array_push(x_508, x_509);
x_511 = lean_box(x_2);
x_512 = lean_array_push(x_510, x_511);
x_513 = lean_box(x_2);
x_514 = lean_array_push(x_512, x_513);
x_515 = lean_box(x_2);
x_516 = lean_array_push(x_514, x_515);
x_517 = lean_box(x_2);
x_518 = lean_array_push(x_516, x_517);
x_519 = lean_byte_array_mk(x_518);
return x_519;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(34u);
x_28 = l_Char_ofNat(x_27);
x_29 = l_instDecidableEqChar(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(92u);
x_31 = l_Char_ofNat(x_30);
x_32 = l_instDecidableEqChar(x_2, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint32_t x_34; uint8_t x_35; 
x_33 = lean_unsigned_to_nat(10u);
x_34 = l_Char_ofNat(x_33);
x_35 = l_instDecidableEqChar(x_2, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint32_t x_37; uint8_t x_38; 
x_36 = lean_unsigned_to_nat(13u);
x_37 = l_Char_ofNat(x_36);
x_38 = l_instDecidableEqChar(x_2, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(32u);
x_40 = lean_uint32_of_nat(x_39);
x_41 = lean_uint32_dec_le(x_40, x_2);
if (x_41 == 0)
{
goto block_26;
}
else
{
lean_object* x_42; uint32_t x_43; uint8_t x_44; 
x_42 = lean_unsigned_to_nat(1114111u);
x_43 = lean_uint32_of_nat(x_42);
x_44 = lean_uint32_dec_le(x_2, x_43);
if (x_44 == 0)
{
goto block_26;
}
else
{
lean_object* x_45; 
x_45 = lean_string_push(x_1, x_2);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_mk_string_unchecked("\\r", 2, 2);
x_47 = lean_string_append(x_1, x_46);
lean_dec(x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_mk_string_unchecked("\\n", 2, 2);
x_49 = lean_string_append(x_1, x_48);
lean_dec(x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_mk_string_unchecked("\\\\", 2, 2);
x_51 = lean_string_append(x_1, x_50);
lean_dec(x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_mk_string_unchecked("\\\"", 2, 2);
x_53 = lean_string_append(x_1, x_52);
lean_dec(x_52);
return x_53;
}
block_26:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_unsigned_to_nat(4096u);
x_5 = lean_unsigned_to_nat(12u);
x_6 = lean_nat_shiftr(x_3, x_5);
x_7 = l_Nat_digitChar(x_6);
lean_dec(x_6);
x_8 = lean_nat_mod(x_3, x_4);
x_9 = lean_unsigned_to_nat(256u);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_shiftr(x_8, x_10);
lean_dec(x_8);
x_12 = l_Nat_digitChar(x_11);
lean_dec(x_11);
x_13 = lean_nat_mod(x_3, x_9);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_nat_shiftr(x_13, x_15);
lean_dec(x_13);
x_17 = l_Nat_digitChar(x_16);
lean_dec(x_16);
x_18 = lean_nat_mod(x_3, x_14);
lean_dec(x_3);
x_19 = l_Nat_digitChar(x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("\\u", 2, 2);
x_21 = lean_string_append(x_1, x_20);
lean_dec(x_20);
x_22 = lean_string_push(x_21, x_7);
x_23 = lean_string_push(x_22, x_12);
x_24 = lean_string_push(x_23, x_17);
x_25 = lean_string_push(x_24, x_19);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
lean_inc(x_2);
x_5 = lean_string_get_byte_fast(x_1, x_2);
x_6 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable;
x_7 = lean_uint8_to_nat(x_5);
x_8 = lean_byte_array_fget(x_6, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_uint8_of_nat(x_9);
x_11 = lean_uint8_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lean_Json_escape_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_7);
x_3 = x_6;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_string_append(x_2, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_foldlAux___at___Lean_Json_escape_spec__0(x_1, x_5, x_6, x_2);
lean_dec(x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lean_Json_escape_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___Lean_Json_escape_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_escape___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_escape(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_mk_string_unchecked("\"", 1, 1);
x_4 = lean_string_append(x_2, x_3);
x_5 = l_Lean_Json_escape(x_1, x_4);
x_6 = lean_string_append(x_5, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_renderString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_renderString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_render_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Json_render(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_render_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at___Lean_Json_render_spec__1(x_1, x_3);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_Json_renderString(x_4, x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked(":", 1, 1);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Json_render(x_5);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
x_1 = x_21;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_render(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("null", 4, 4);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_string_unchecked("false", 5, 5);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_mk_string_unchecked("true", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 2:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l_Lean_JsonNumber_toString(x_10);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_JsonNumber_toString(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
case 3:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_mk_string_unchecked("", 0, 0);
x_18 = l_Lean_Json_renderString(x_16, x_17);
lean_dec(x_16);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = l_Lean_Json_renderString(x_19, x_20);
lean_dec(x_19);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
case 4:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; size_t x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_array_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_usize_of_nat(x_26);
x_28 = l_Array_mapMUnsafe_map___at___Lean_Json_render_spec__0(x_25, x_27, x_24);
x_29 = lean_array_to_list(x_28);
x_30 = lean_mk_string_unchecked(",", 1, 1);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_30);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_29, x_32);
x_34 = lean_mk_string_unchecked("[", 1, 1);
x_35 = lean_mk_string_unchecked("]", 1, 1);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_34);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
return x_44;
}
else
{
lean_object* x_46; size_t x_47; lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_array_size(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_usize_of_nat(x_48);
x_50 = l_Array_mapMUnsafe_map___at___Lean_Json_render_spec__0(x_47, x_49, x_46);
x_51 = lean_array_to_list(x_50);
x_52 = lean_mk_string_unchecked(",", 1, 1);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_51, x_55);
x_57 = lean_mk_string_unchecked("[", 1, 1);
x_58 = lean_mk_string_unchecked("]", 1, 1);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_to_int(x_59);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_57);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_unbox(x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_68);
return x_67;
}
}
default: 
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_1);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_box(0);
x_72 = l_Lean_RBNode_fold___at___Lean_Json_render_spec__1(x_71, x_70);
x_73 = lean_mk_string_unchecked(",", 1, 1);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_73);
x_74 = lean_box(1);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_72, x_75);
x_77 = lean_mk_string_unchecked("{", 1, 1);
x_78 = lean_mk_string_unchecked("}", 1, 1);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_to_int(x_79);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_77);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_76);
x_83 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_87, 0, x_85);
x_88 = lean_unbox(x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_88);
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = l_Lean_RBNode_fold___at___Lean_Json_render_spec__1(x_90, x_89);
x_92 = lean_mk_string_unchecked(",", 1, 1);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_box(1);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_91, x_95);
x_97 = lean_mk_string_unchecked("{", 1, 1);
x_98 = lean_mk_string_unchecked("}", 1, 1);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_to_int(x_99);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_97);
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_render_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_render_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_pretty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Json_render(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_3, x_2, x_4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_compress_go_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Json_compress_go_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("null", 4, 4);
x_7 = lean_string_append(x_1, x_6);
lean_dec(x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
case 1:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_mk_string_unchecked("false", 5, 5);
x_12 = lean_string_append(x_1, x_11);
lean_dec(x_11);
x_1 = x_12;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_mk_string_unchecked("true", 4, 4);
x_16 = lean_string_append(x_1, x_15);
lean_dec(x_15);
x_1 = x_16;
x_2 = x_14;
goto _start;
}
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Lean_JsonNumber_toString(x_19);
x_21 = lean_string_append(x_1, x_20);
lean_dec(x_20);
x_1 = x_21;
x_2 = x_18;
goto _start;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l_Lean_Json_renderString(x_24, x_1);
lean_dec(x_24);
x_1 = x_25;
x_2 = x_23;
goto _start;
}
case 4:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_mk_string_unchecked("[", 1, 1);
x_31 = lean_string_append(x_1, x_30);
lean_dec(x_30);
x_32 = lean_array_size(x_29);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_usize_of_nat(x_33);
x_35 = l_Array_mapMUnsafe_map___at___Lean_Json_compress_go_spec__0(x_32, x_34, x_29);
x_36 = lean_box(2);
lean_ctor_set(x_2, 0, x_36);
x_37 = lean_array_get_size(x_35);
x_38 = lean_nat_dec_lt(x_33, x_37);
if (x_38 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
x_1 = x_31;
goto _start;
}
else
{
size_t x_40; lean_object* x_41; 
x_40 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_41 = l_Array_foldrMUnsafe_fold___at___Lean_Json_compress_go_spec__1(x_35, x_40, x_34, x_2);
lean_dec(x_35);
x_1 = x_31;
x_2 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_mk_string_unchecked("[", 1, 1);
x_46 = lean_string_append(x_1, x_45);
lean_dec(x_45);
x_47 = lean_array_size(x_44);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_usize_of_nat(x_48);
x_50 = l_Array_mapMUnsafe_map___at___Lean_Json_compress_go_spec__0(x_47, x_49, x_44);
x_51 = lean_box(2);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
x_53 = lean_array_get_size(x_50);
x_54 = lean_nat_dec_lt(x_48, x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_50);
x_1 = x_46;
x_2 = x_52;
goto _start;
}
else
{
size_t x_56; lean_object* x_57; 
x_56 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_57 = l_Array_foldrMUnsafe_fold___at___Lean_Json_compress_go_spec__1(x_50, x_56, x_49, x_52);
lean_dec(x_50);
x_1 = x_46;
x_2 = x_57;
goto _start;
}
}
}
default: 
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_ctor_get(x_2, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_4, 0);
lean_inc(x_62);
lean_dec(x_4);
x_63 = lean_mk_string_unchecked("{", 1, 1);
x_64 = lean_string_append(x_1, x_63);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2(x_65, x_62);
lean_dec(x_62);
x_67 = lean_box(4);
lean_ctor_set(x_2, 1, x_65);
lean_ctor_set(x_2, 0, x_67);
x_68 = l_List_appendTR(lean_box(0), x_66, x_2);
x_69 = l_List_appendTR(lean_box(0), x_68, x_60);
x_1 = x_64;
x_2 = x_69;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_dec(x_2);
x_72 = lean_ctor_get(x_4, 0);
lean_inc(x_72);
lean_dec(x_4);
x_73 = lean_mk_string_unchecked("{", 1, 1);
x_74 = lean_string_append(x_1, x_73);
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2(x_75, x_72);
lean_dec(x_72);
x_77 = lean_box(4);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
x_79 = l_List_appendTR(lean_box(0), x_76, x_78);
x_80 = l_List_appendTR(lean_box(0), x_79, x_71);
x_1 = x_74;
x_2 = x_80;
goto _start;
}
}
}
}
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_83 = x_2;
} else {
 lean_dec_ref(x_2);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_3, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_85 = x_3;
} else {
 lean_dec_ref(x_3);
 x_85 = lean_box(0);
}
if (lean_obj_tag(x_82) == 0)
{
x_86 = x_82;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 2)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_85);
lean_dec(x_83);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_84);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_82);
x_2 = x_95;
goto _start;
}
else
{
lean_dec(x_93);
x_86 = x_82;
goto block_92;
}
}
block_92:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_85;
 lean_ctor_set_tag(x_87, 0);
}
lean_ctor_set(x_87, 0, x_84);
x_88 = lean_box(5);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_2 = x_90;
goto _start;
}
}
case 2:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
lean_dec(x_2);
x_98 = lean_mk_string_unchecked("]", 1, 1);
x_99 = lean_string_append(x_1, x_98);
lean_dec(x_98);
x_1 = x_99;
x_2 = x_97;
goto _start;
}
case 3:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_102 = x_2;
} else {
 lean_dec_ref(x_2);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_3, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_3, 1);
lean_inc(x_104);
lean_dec(x_3);
if (lean_obj_tag(x_101) == 0)
{
x_105 = x_101;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_101, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 4)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_102);
x_116 = l_Lean_Json_renderString(x_103, x_1);
lean_dec(x_103);
x_117 = lean_mk_string_unchecked(":", 1, 1);
x_118 = lean_string_append(x_116, x_117);
lean_dec(x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_104);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_101);
x_1 = x_118;
x_2 = x_120;
goto _start;
}
else
{
lean_dec(x_115);
x_105 = x_101;
goto block_114;
}
}
block_114:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = l_Lean_Json_renderString(x_103, x_1);
lean_dec(x_103);
x_107 = lean_mk_string_unchecked(":", 1, 1);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_110 = lean_box(5);
if (lean_is_scalar(x_102)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_102;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_1 = x_108;
x_2 = x_112;
goto _start;
}
}
case 4:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_2, 1);
lean_inc(x_122);
lean_dec(x_2);
x_123 = lean_mk_string_unchecked("}", 1, 1);
x_124 = lean_string_append(x_1, x_123);
lean_dec(x_123);
x_1 = x_124;
x_2 = x_122;
goto _start;
}
default: 
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_dec(x_2);
x_127 = lean_mk_string_unchecked(",", 1, 1);
x_128 = lean_string_append(x_1, x_127);
lean_dec(x_127);
x_1 = x_128;
x_2 = x_126;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_compress_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_compress_go_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Json_compress_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Json_compress_go_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___Lean_Json_compress_go_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_compress(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Json_compress_go(x_2, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Json_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_render), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_instToString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_instToString___lam__0), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Json_Printer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable = _init_l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable();
lean_mark_persistent(l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeTable);
l_Lean_Json_instToFormat = _init_l_Lean_Json_instToFormat();
lean_mark_persistent(l_Lean_Json_instToFormat);
l_Lean_Json_instToString = _init_l_Lean_Json_instToString();
lean_mark_persistent(l_Lean_Json_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
