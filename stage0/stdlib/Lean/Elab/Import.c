// Lean compiler output
// Module: Lean.Elab.Import
// Imports: Lean.Parser.Module Lean.Util.Paths Lean.CoreM
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_print_imports(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_processHeaderCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImportSrcs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* lean_print_import_srcs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_getSrcSearchPath(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImportSrcs_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___Lean_Elab_printImports_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2_spec__2(size_t, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedImport;
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_IO_print___at___IO_println___at___Lean_Environment_displayStats_spec__2_spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_processHeaderCore_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImports_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_findLean(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_inServer;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImports_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__0(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Syntax_getPos_x3f(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_HeaderSyntax_startPos(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_HeaderSyntax_isModule(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedImport;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_29; 
x_5 = lean_mk_string_unchecked("import", 6, 6);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Module", 6, 6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_5);
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_11);
x_29 = l_Lean_Syntax_isOfKind(x_11, x_10);
lean_dec(x_10);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_30 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_31 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_32 = lean_unsigned_to_nat(27u);
x_33 = lean_unsigned_to_nat(13u);
x_34 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_34);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_35);
x_14 = x_36;
goto block_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_56; lean_object* x_57; lean_object* x_83; uint8_t x_84; 
x_37 = lean_unsigned_to_nat(0u);
x_56 = lean_unsigned_to_nat(2u);
x_83 = l_Lean_Syntax_getArg(x_11, x_37);
x_84 = l_Lean_Syntax_isNone(x_83);
if (x_84 == 0)
{
uint8_t x_85; 
lean_inc(x_83);
x_85 = l_Lean_Syntax_matchesNull(x_83, x_6);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_83);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_86 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_87 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_88 = lean_unsigned_to_nat(27u);
x_89 = lean_unsigned_to_nat(13u);
x_90 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_91 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_86, x_87, x_88, x_89, x_90);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_86);
x_92 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_91);
x_14 = x_92;
goto block_19;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = l_Lean_Syntax_getArg(x_83, x_37);
lean_dec(x_83);
x_94 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_95 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_94);
lean_inc(x_93);
x_96 = l_Lean_Syntax_isOfKind(x_93, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_98 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_99 = lean_unsigned_to_nat(27u);
x_100 = lean_unsigned_to_nat(13u);
x_101 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_102 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_97, x_98, x_99, x_100, x_101);
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_97);
x_103 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_102);
x_14 = x_103;
goto block_19;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Syntax_getArg(x_93, x_37);
lean_dec(x_93);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_57 = x_105;
goto block_82;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_83);
x_106 = lean_box(0);
x_57 = x_106;
goto block_82;
}
block_55:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(4u);
x_41 = l_Lean_Syntax_getArg(x_11, x_40);
x_42 = l_Lean_Syntax_matchesNull(x_41, x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_11);
x_43 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_44 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_45 = lean_unsigned_to_nat(27u);
x_46 = lean_unsigned_to_nat(13u);
x_47 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_48 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_43, x_44, x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_43);
x_49 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_48);
x_14 = x_49;
goto block_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_unsigned_to_nat(3u);
x_51 = l_Lean_Syntax_getArg(x_11, x_50);
lean_dec(x_11);
x_52 = l_Lean_Syntax_getId(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_box(0);
x_54 = lean_unbox(x_53);
x_20 = x_38;
x_21 = x_52;
x_22 = x_42;
x_23 = x_54;
goto block_28;
}
else
{
lean_dec(x_39);
x_20 = x_38;
x_21 = x_52;
x_22 = x_42;
x_23 = x_42;
goto block_28;
}
}
}
block_82:
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Syntax_getArg(x_11, x_56);
x_59 = l_Lean_Syntax_isNone(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_inc(x_58);
x_60 = l_Lean_Syntax_matchesNull(x_58, x_6);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_62 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_63 = lean_unsigned_to_nat(27u);
x_64 = lean_unsigned_to_nat(13u);
x_65 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_66 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_61, x_62, x_63, x_64, x_65);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
x_67 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_66);
x_14 = x_67;
goto block_19;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = l_Lean_Syntax_getArg(x_58, x_37);
lean_dec(x_58);
x_69 = lean_mk_string_unchecked("all", 3, 3);
x_70 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_69);
lean_inc(x_68);
x_71 = l_Lean_Syntax_isOfKind(x_68, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_57);
lean_dec(x_11);
x_72 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_73 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_74 = lean_unsigned_to_nat(27u);
x_75 = lean_unsigned_to_nat(13u);
x_76 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_77 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_72, x_73, x_74, x_75, x_76);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
x_78 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_77);
x_14 = x_78;
goto block_19;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Syntax_getArg(x_68, x_37);
lean_dec(x_68);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_38 = x_57;
x_39 = x_80;
goto block_55;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_81 = lean_box(0);
x_38 = x_57;
x_39 = x_81;
goto block_55;
}
}
}
block_19:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_6);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_14);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
block_28:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 1, x_22);
x_14 = x_24;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_23);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_27);
x_14 = x_26;
goto block_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_29; 
x_5 = lean_mk_string_unchecked("import", 6, 6);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Module", 6, 6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_5);
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_11);
x_29 = l_Lean_Syntax_isOfKind(x_11, x_10);
lean_dec(x_10);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_30 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_31 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_32 = lean_unsigned_to_nat(27u);
x_33 = lean_unsigned_to_nat(13u);
x_34 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_34);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_35);
x_14 = x_36;
goto block_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_56; lean_object* x_57; lean_object* x_83; uint8_t x_84; 
x_37 = lean_unsigned_to_nat(0u);
x_56 = lean_unsigned_to_nat(2u);
x_83 = l_Lean_Syntax_getArg(x_11, x_37);
x_84 = l_Lean_Syntax_isNone(x_83);
if (x_84 == 0)
{
uint8_t x_85; 
lean_inc(x_83);
x_85 = l_Lean_Syntax_matchesNull(x_83, x_6);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_83);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_86 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_87 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_88 = lean_unsigned_to_nat(27u);
x_89 = lean_unsigned_to_nat(13u);
x_90 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_91 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_86, x_87, x_88, x_89, x_90);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_86);
x_92 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_91);
x_14 = x_92;
goto block_19;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = l_Lean_Syntax_getArg(x_83, x_37);
lean_dec(x_83);
x_94 = lean_mk_string_unchecked("private", 7, 7);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_95 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_94);
lean_inc(x_93);
x_96 = l_Lean_Syntax_isOfKind(x_93, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_98 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_99 = lean_unsigned_to_nat(27u);
x_100 = lean_unsigned_to_nat(13u);
x_101 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_102 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_97, x_98, x_99, x_100, x_101);
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_97);
x_103 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_102);
x_14 = x_103;
goto block_19;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Syntax_getArg(x_93, x_37);
lean_dec(x_93);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_57 = x_105;
goto block_82;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_83);
x_106 = lean_box(0);
x_57 = x_106;
goto block_82;
}
block_55:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(4u);
x_41 = l_Lean_Syntax_getArg(x_11, x_40);
x_42 = l_Lean_Syntax_matchesNull(x_41, x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_11);
x_43 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_44 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_45 = lean_unsigned_to_nat(27u);
x_46 = lean_unsigned_to_nat(13u);
x_47 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_48 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_43, x_44, x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_43);
x_49 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_48);
x_14 = x_49;
goto block_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_unsigned_to_nat(3u);
x_51 = l_Lean_Syntax_getArg(x_11, x_50);
lean_dec(x_11);
x_52 = l_Lean_Syntax_getId(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_box(0);
x_54 = lean_unbox(x_53);
x_20 = x_38;
x_21 = x_52;
x_22 = x_42;
x_23 = x_54;
goto block_28;
}
else
{
lean_dec(x_39);
x_20 = x_38;
x_21 = x_52;
x_22 = x_42;
x_23 = x_42;
goto block_28;
}
}
}
block_82:
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Syntax_getArg(x_11, x_56);
x_59 = l_Lean_Syntax_isNone(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_inc(x_58);
x_60 = l_Lean_Syntax_matchesNull(x_58, x_6);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_62 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_63 = lean_unsigned_to_nat(27u);
x_64 = lean_unsigned_to_nat(13u);
x_65 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_66 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_61, x_62, x_63, x_64, x_65);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
x_67 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_66);
x_14 = x_67;
goto block_19;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = l_Lean_Syntax_getArg(x_58, x_37);
lean_dec(x_58);
x_69 = lean_mk_string_unchecked("all", 3, 3);
x_70 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_69);
lean_inc(x_68);
x_71 = l_Lean_Syntax_isOfKind(x_68, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_57);
lean_dec(x_11);
x_72 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_73 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_74 = lean_unsigned_to_nat(27u);
x_75 = lean_unsigned_to_nat(13u);
x_76 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_77 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_72, x_73, x_74, x_75, x_76);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
x_78 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__1(x_77);
x_14 = x_78;
goto block_19;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Syntax_getArg(x_68, x_37);
lean_dec(x_68);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_38 = x_57;
x_39 = x_80;
goto block_55;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_81 = lean_box(0);
x_38 = x_57;
x_39 = x_81;
goto block_55;
}
}
}
block_19:
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_usize_of_nat(x_6);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_14);
x_18 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2_spec__2(x_1, x_16, x_17);
return x_18;
}
block_28:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 1, x_22);
x_14 = x_24;
goto block_19;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_23);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_27);
x_14 = x_26;
goto block_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Module", 6, 6);
x_5 = lean_mk_string_unchecked("header", 6, 6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_9 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_10 = lean_unsigned_to_nat(28u);
x_11 = lean_unsigned_to_nat(9u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__0(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_26; lean_object* x_27; lean_object* x_65; uint8_t x_66; 
x_15 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Syntax_getArg(x_1, x_15);
x_66 = l_Lean_Syntax_isNone(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_unsigned_to_nat(1u);
lean_inc(x_65);
x_68 = l_Lean_Syntax_matchesNull(x_65, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_65);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_70 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_71 = lean_unsigned_to_nat(28u);
x_72 = lean_unsigned_to_nat(9u);
x_73 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_74 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_69, x_70, x_71, x_72, x_73);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_69);
x_75 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__0(x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = l_Lean_Syntax_getArg(x_65, x_15);
lean_dec(x_65);
x_77 = lean_mk_string_unchecked("moduleTk", 8, 8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_78 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_77);
x_79 = l_Lean_Syntax_isOfKind(x_76, x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_81 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_82 = lean_unsigned_to_nat(28u);
x_83 = lean_unsigned_to_nat(9u);
x_84 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_85 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_80, x_81, x_82, x_83, x_84);
lean_dec(x_84);
lean_dec(x_81);
lean_dec(x_80);
x_86 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__0(x_85);
return x_86;
}
else
{
goto block_64;
}
}
}
else
{
lean_dec(x_65);
goto block_64;
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_size(x_16);
x_19 = lean_usize_of_nat(x_15);
x_20 = l_Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2(x_18, x_19, x_16);
x_21 = l_Array_append(lean_box(0), x_17, x_20);
lean_dec(x_20);
return x_21;
}
block_25:
{
lean_object* x_24; 
x_24 = lean_mk_empty_array_with_capacity(x_15);
x_16 = x_23;
x_17 = x_24;
goto block_22;
}
block_38:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
lean_dec(x_1);
x_30 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
if (lean_obj_tag(x_27) == 0)
{
if (x_7 == 0)
{
x_23 = x_30;
goto block_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_mk_string_unchecked("Init", 4, 4);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 1, x_7);
x_36 = lean_mk_empty_array_with_capacity(x_26);
x_37 = lean_array_push(x_36, x_34);
x_16 = x_30;
x_17 = x_37;
goto block_22;
}
}
else
{
lean_dec(x_27);
x_23 = x_30;
goto block_25;
}
}
block_64:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
x_41 = l_Lean_Syntax_isNone(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_inc(x_40);
x_42 = l_Lean_Syntax_matchesNull(x_40, x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_44 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_45 = lean_unsigned_to_nat(28u);
x_46 = lean_unsigned_to_nat(9u);
x_47 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_48 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_43, x_44, x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_43);
x_49 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__0(x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_Syntax_getArg(x_40, x_15);
lean_dec(x_40);
x_51 = lean_mk_string_unchecked("prelude", 7, 7);
x_52 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_51);
lean_inc(x_50);
x_53 = l_Lean_Syntax_isOfKind(x_50, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_50);
lean_dec(x_1);
x_54 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
x_55 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
x_56 = lean_unsigned_to_nat(28u);
x_57 = lean_unsigned_to_nat(9u);
x_58 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_59 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_54, x_55, x_56, x_57, x_58);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
x_60 = l_panic___at___Lean_Elab_HeaderSyntax_imports_spec__0(x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Syntax_getArg(x_50, x_15);
lean_dec(x_50);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_26 = x_39;
x_27 = x_62;
goto block_38;
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_box(0);
x_26 = x_39;
x_27 = x_63;
goto block_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_HeaderSyntax_imports_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_HeaderSyntax_imports(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_processHeaderCore_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_24; uint8_t x_26; uint8_t x_31; 
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = lean_array_uget(x_3, x_5);
if (x_1 == 0)
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
if (x_38 == 0)
{
x_31 = x_38;
goto block_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_18);
lean_dec(x_2);
x_39 = lean_mk_string_unchecked("cannot use `import all` without `module`", 40, 40);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
x_31 = x_43;
goto block_37;
}
block_23:
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*1 + 1);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_mk_string_unchecked("cannot use `private import` without `module`", 44, 44);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
x_8 = x_17;
x_9 = x_7;
goto block_14;
}
}
block_25:
{
if (x_1 == 0)
{
goto block_23;
}
else
{
if (x_24 == 0)
{
lean_dec(x_18);
x_8 = x_17;
x_9 = x_7;
goto block_14;
}
else
{
goto block_23;
}
}
}
block_30:
{
if (x_26 == 0)
{
x_24 = x_26;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_2);
x_27 = lean_mk_string_unchecked("cannot use `import all` across module path roots", 48, 48);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
block_37:
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
if (x_32 == 0)
{
x_26 = x_32;
goto block_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_inc(x_2);
x_33 = l_Lean_Name_getRoot(x_2);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
x_35 = l_Lean_Name_getRoot(x_34);
x_36 = lean_name_eq(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_36 == 0)
{
x_26 = x_32;
goto block_30;
}
else
{
x_24 = x_31;
goto block_25;
}
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint32_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_20; lean_object* x_21; lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(1);
if (x_3 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_box(2);
x_65 = lean_unbox(x_64);
x_48 = x_65;
goto block_63;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Elab_inServer;
x_67 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_box(0);
x_69 = lean_unbox(x_68);
x_48 = x_69;
goto block_63;
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_box(1);
x_71 = lean_unbox(x_70);
x_48 = x_71;
goto block_63;
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Environment_setMainModule(x_13, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
block_46:
{
lean_object* x_22; uint32_t x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_uint32_of_nat(x_22);
x_24 = lean_mk_empty_environment(x_23, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = l_Lean_FileMap_toPosition(x_27, x_1);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = lean_box(2);
x_33 = lean_mk_string_unchecked("", 0, 0);
x_34 = lean_io_error_to_string(x_20);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_unbox(x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_38);
x_39 = lean_unbox(x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*5 + 1, x_39);
x_40 = lean_unbox(x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*5 + 2, x_40);
x_41 = l_Lean_MessageLog_add(x_37, x_5);
x_13 = x_25;
x_14 = x_41;
x_15 = x_26;
goto block_19;
}
else
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
block_63:
{
lean_object* x_49; size_t x_50; lean_object* x_51; size_t x_52; lean_object* x_53; 
x_49 = lean_box(0);
x_50 = lean_array_size(x_2);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_usize_of_nat(x_51);
lean_inc(x_10);
x_53 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_processHeaderCore_spec__0(x_3, x_10, x_2, x_50, x_52, x_49, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_unbox(x_47);
x_56 = l_Lean_importModules(x_2, x_4, x_7, x_8, x_9, x_55, x_48, x_11, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_6);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_13 = x_57;
x_14 = x_5;
x_15 = x_58;
goto block_19;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_20 = x_59;
x_21 = x_60;
goto block_46;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_dec(x_53);
x_20 = x_61;
x_21 = x_62;
goto block_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_processHeaderCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_processHeaderCore_spec__0(x_8, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint32_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_uint32(x_7);
lean_dec(x_7);
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l_Lean_Elab_processHeaderCore(x_1, x_2, x_13, x_4, x_5, x_6, x_14, x_8, x_15, x_10, x_11, x_12);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_HeaderSyntax_startPos(x_1);
lean_inc(x_1);
x_11 = l_Lean_Elab_HeaderSyntax_imports(x_1);
x_12 = l_Lean_Elab_HeaderSyntax_isModule(x_1);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_processHeaderCore(x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_9);
lean_dec(x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l_Lean_Elab_processHeader(x_1, x_2, x_3, x_4, x_10, x_6, x_11, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_57; 
x_57 = lean_mk_string_unchecked("<input>", 7, 7);
x_4 = x_57;
goto block_56;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec(x_2);
x_4 = x_58;
goto block_56;
}
block_56:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Parser_mkInputContext(x_1, x_4, x_6);
lean_inc(x_7);
x_8 = l_Lean_Parser_parseHeader(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = l_Lean_Elab_HeaderSyntax_imports(x_14);
x_19 = lean_ctor_get(x_7, 2);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_FileMap_toPosition(x_19, x_20);
lean_dec(x_20);
lean_ctor_set(x_10, 0, x_21);
lean_ctor_set(x_9, 0, x_18);
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = l_Lean_Elab_HeaderSyntax_imports(x_14);
x_25 = lean_ctor_get(x_7, 2);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_FileMap_toPosition(x_25, x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_9, 1, x_28);
lean_ctor_set(x_9, 0, x_24);
return x_8;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_32 = x_10;
} else {
 lean_dec_ref(x_10);
 x_32 = lean_box(0);
}
x_33 = l_Lean_Elab_HeaderSyntax_imports(x_29);
x_34 = lean_ctor_get(x_7, 2);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_FileMap_toPosition(x_34, x_35);
lean_dec(x_35);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_dec(x_8);
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_41 = x_9;
} else {
 lean_dec_ref(x_9);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_44 = x_10;
} else {
 lean_dec_ref(x_10);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Elab_HeaderSyntax_imports(x_40);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Lean_FileMap_toPosition(x_46, x_47);
lean_dec(x_47);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
if (lean_is_scalar(x_41)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_41;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_println___at___Lean_Elab_printImports_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(10u);
x_4 = l_Char_ofNat(x_3);
x_5 = lean_string_push(x_1, x_4);
x_6 = l_IO_print___at___IO_println___at___Lean_Environment_displayStats_spec__2_spec__2(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImports_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_findOLean(x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_IO_println___at___Lean_Elab_printImports_spec__0(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_15;
x_5 = x_14;
goto _start;
}
else
{
return x_13;
}
}
else
{
uint8_t x_20; 
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
LEAN_EXPORT lean_object* lean_print_imports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_parseImports(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_array_size(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_usize_of_nat(x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImports_spec__1(x_7, x_9, x_11, x_8, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
return x_12;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImports_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImports_spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImportSrcs_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_findLean(x_1, x_10, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_IO_println___at___Lean_Elab_printImports_spec__0(x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_16;
x_6 = x_15;
goto _start;
}
else
{
lean_dec(x_1);
return x_14;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_print_import_srcs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getSrcSearchPath(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_parseImports(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; size_t x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_array_size(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_usize_of_nat(x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImportSrcs_spec__0(x_5, x_10, x_12, x_14, x_11, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
return x_15;
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImportSrcs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_printImportSrcs_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
