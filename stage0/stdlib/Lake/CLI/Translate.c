// Lean compiler output
// Module: Lake.CLI.Translate
// Imports: Lake.Config.Lang Lake.Config.Package Lake.CLI.Translate.Toml Lake.CLI.Translate.Lean Lake.Load.Lean.Elab
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats(lean_object*);
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_inheritedTraceOptions;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_mkLeanConfig(lean_object*);
lean_object* l_Lake_Package_mkTomlConfig(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lake_Toml_ppTable(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_5);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; size_t x_4; lean_object* x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_array_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(x_4, x_6, x_3);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_array_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
x_14 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(x_11, x_13, x_10);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
case 3:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_erase_macro_scopes(x_17);
lean_ctor_set(x_1, 2, x_18);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = lean_erase_macro_scopes(x_21);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
return x_24;
}
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (x_2 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; 
x_18 = lean_mk_string_unchecked("Lake", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_box(0);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_unbox(x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1 + 1, x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_22);
x_28 = lean_box(0);
x_29 = lean_unsigned_to_nat(1024u);
x_30 = lean_uint32_of_nat(x_29);
x_31 = l_Lake_importModulesUsingCache(x_27, x_28, x_30, x_4);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_mk_string_unchecked("_uniq", 5, 5);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_unsigned_to_nat(5u);
x_37 = lean_usize_of_nat(x_36);
x_38 = lean_usize_to_nat(x_37);
x_39 = lean_nat_pow(x_35, x_38);
lean_dec(x_38);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = lean_usize_to_nat(x_40);
x_42 = lean_mk_empty_array_with_capacity(x_41);
lean_dec(x_41);
lean_inc(x_42);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
lean_inc(x_42);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_42);
x_47 = lean_io_get_num_heartbeats(x_33);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Name_mkStr1(x_34);
x_53 = lean_uint64_of_nat(x_51);
lean_inc(x_42);
x_54 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set_usize(x_54, 4, x_37);
lean_inc(x_44);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_44);
lean_inc(x_42);
x_56 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_42);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set_usize(x_56, 4, x_37);
x_57 = lean_box(0);
lean_inc(x_44);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_44);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_44);
x_60 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_42);
lean_ctor_set(x_60, 2, x_51);
lean_ctor_set(x_60, 3, x_51);
lean_ctor_set_usize(x_60, 4, x_37);
lean_ctor_set(x_47, 1, x_25);
lean_ctor_set(x_47, 0, x_52);
x_61 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set_uint64(x_61, sizeof(void*)*1, x_53);
lean_inc(x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_55);
lean_inc(x_56);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_56);
lean_ctor_set(x_63, 2, x_57);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
x_65 = lean_unbox(x_21);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_65);
x_66 = lean_mk_empty_array_with_capacity(x_51);
lean_inc(x_62);
x_67 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_67, 0, x_32);
lean_ctor_set(x_67, 1, x_35);
lean_ctor_set(x_67, 2, x_47);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_62);
lean_ctor_set(x_67, 5, x_63);
lean_ctor_set(x_67, 6, x_64);
lean_ctor_set(x_67, 7, x_66);
x_68 = lean_st_mk_ref(x_67, x_50);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_inheritedTraceOptions;
x_72 = lean_st_ref_get(x_71, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_get(x_69, x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_165; uint8_t x_166; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = l_Lake_Package_mkLeanConfig(x_1);
x_80 = lean_mk_string_unchecked("", 0, 0);
x_81 = l_Array_empty(lean_box(0));
x_82 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_79);
lean_inc(x_80);
lean_ctor_set(x_75, 1, x_81);
lean_ctor_set(x_75, 0, x_80);
x_83 = lean_box(0);
x_84 = lean_box(0);
x_85 = lean_box(0);
x_86 = l_Lean_Core_getMaxHeartbeats(x_28);
x_87 = lean_box(0);
x_88 = l_Lean_diagnostics;
x_89 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_28, x_88);
x_165 = lean_ctor_get(x_77, 0);
lean_inc(x_165);
lean_dec(x_77);
x_166 = l_Lean_Kernel_isDiagnosticsEnabled(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
if (x_89 == 0)
{
lean_dec(x_62);
lean_inc(x_69);
x_90 = x_69;
x_91 = x_78;
goto block_149;
}
else
{
goto block_164;
}
}
else
{
if (x_89 == 0)
{
goto block_164;
}
else
{
lean_dec(x_62);
lean_inc(x_69);
x_90 = x_69;
x_91 = x_78;
goto block_149;
}
}
block_149:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_92 = l_Lean_maxRecDepth;
x_93 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_28, x_92);
x_94 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_94, 0, x_80);
lean_ctor_set(x_94, 1, x_75);
lean_ctor_set(x_94, 2, x_28);
lean_ctor_set(x_94, 3, x_51);
lean_ctor_set(x_94, 4, x_93);
lean_ctor_set(x_94, 5, x_83);
lean_ctor_set(x_94, 6, x_84);
lean_ctor_set(x_94, 7, x_85);
lean_ctor_set(x_94, 8, x_49);
lean_ctor_set(x_94, 9, x_86);
lean_ctor_set(x_94, 10, x_25);
lean_ctor_set(x_94, 11, x_87);
lean_ctor_set(x_94, 12, x_73);
lean_ctor_set_uint8(x_94, sizeof(void*)*13, x_89);
x_95 = lean_unbox(x_20);
lean_ctor_set_uint8(x_94, sizeof(void*)*13 + 1, x_95);
x_96 = l_Lean_PrettyPrinter_ppModule(x_82, x_94, x_90, x_91);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
x_100 = lean_st_ref_get(x_69, x_99);
lean_dec(x_69);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
x_103 = lean_unsigned_to_nat(120u);
x_104 = lean_format_pretty(x_98, x_103, x_51, x_51);
x_105 = lean_string_utf8_byte_size(x_104);
x_106 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_104, x_105, x_51);
x_107 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_104, x_106, x_105);
x_108 = lean_string_utf8_extract(x_104, x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
x_109 = lean_mk_string_unchecked("\n", 1, 1);
x_110 = lean_string_append(x_108, x_109);
lean_dec(x_109);
lean_ctor_set(x_96, 1, x_3);
lean_ctor_set(x_96, 0, x_110);
lean_ctor_set(x_100, 0, x_96);
return x_100;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_dec(x_100);
x_112 = lean_unsigned_to_nat(120u);
x_113 = lean_format_pretty(x_98, x_112, x_51, x_51);
x_114 = lean_string_utf8_byte_size(x_113);
x_115 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_113, x_114, x_51);
x_116 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_113, x_115, x_114);
x_117 = lean_string_utf8_extract(x_113, x_115, x_116);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
x_118 = lean_mk_string_unchecked("\n", 1, 1);
x_119 = lean_string_append(x_117, x_118);
lean_dec(x_118);
lean_ctor_set(x_96, 1, x_3);
lean_ctor_set(x_96, 0, x_119);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_96);
lean_ctor_set(x_120, 1, x_111);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_121 = lean_ctor_get(x_96, 0);
x_122 = lean_ctor_get(x_96, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_96);
x_123 = lean_st_ref_get(x_69, x_122);
lean_dec(x_69);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_unsigned_to_nat(120u);
x_127 = lean_format_pretty(x_121, x_126, x_51, x_51);
x_128 = lean_string_utf8_byte_size(x_127);
x_129 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_127, x_128, x_51);
x_130 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_127, x_129, x_128);
x_131 = lean_string_utf8_extract(x_127, x_129, x_130);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_127);
x_132 = lean_mk_string_unchecked("\n", 1, 1);
x_133 = lean_string_append(x_131, x_132);
lean_dec(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_3);
if (lean_is_scalar(x_125)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_125;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_124);
return x_135;
}
}
else
{
lean_object* x_136; 
lean_dec(x_69);
x_136 = lean_ctor_get(x_96, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_96, 1);
lean_inc(x_137);
lean_dec(x_96);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_MessageData_toString(x_138, x_137);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_142, 0, x_140);
x_5 = x_142;
x_6 = x_141;
goto block_17;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_96, 1);
lean_inc(x_143);
lean_dec(x_96);
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
lean_dec(x_136);
x_145 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_146 = l___private_Init_Data_Repr_0__Nat_reprFast(x_144);
x_147 = lean_string_append(x_145, x_146);
lean_dec(x_146);
x_148 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_5 = x_148;
x_6 = x_143;
goto block_17;
}
}
}
block_164:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_150 = lean_st_ref_take(x_69, x_78);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = l_Lean_Kernel_enableDiag(x_153, x_89);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 5);
lean_inc(x_158);
x_159 = lean_ctor_get(x_151, 6);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 7);
lean_inc(x_160);
lean_dec(x_151);
x_161 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set(x_161, 4, x_62);
lean_ctor_set(x_161, 5, x_158);
lean_ctor_set(x_161, 6, x_159);
lean_ctor_set(x_161, 7, x_160);
x_162 = lean_st_ref_set(x_69, x_161, x_152);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_69);
x_90 = x_69;
x_91 = x_163;
goto block_149;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_233; uint8_t x_234; 
x_167 = lean_ctor_get(x_75, 0);
x_168 = lean_ctor_get(x_75, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_75);
x_169 = l_Lake_Package_mkLeanConfig(x_1);
x_170 = lean_mk_string_unchecked("", 0, 0);
x_171 = l_Array_empty(lean_box(0));
x_172 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_169);
lean_inc(x_170);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_box(0);
x_175 = lean_box(0);
x_176 = lean_box(0);
x_177 = l_Lean_Core_getMaxHeartbeats(x_28);
x_178 = lean_box(0);
x_179 = l_Lean_diagnostics;
x_180 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_28, x_179);
x_233 = lean_ctor_get(x_167, 0);
lean_inc(x_233);
lean_dec(x_167);
x_234 = l_Lean_Kernel_isDiagnosticsEnabled(x_233);
lean_dec(x_233);
if (x_234 == 0)
{
if (x_180 == 0)
{
lean_dec(x_62);
lean_inc(x_69);
x_181 = x_69;
x_182 = x_168;
goto block_217;
}
else
{
goto block_232;
}
}
else
{
if (x_180 == 0)
{
goto block_232;
}
else
{
lean_dec(x_62);
lean_inc(x_69);
x_181 = x_69;
x_182 = x_168;
goto block_217;
}
}
block_217:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; 
x_183 = l_Lean_maxRecDepth;
x_184 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_28, x_183);
x_185 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_185, 0, x_170);
lean_ctor_set(x_185, 1, x_173);
lean_ctor_set(x_185, 2, x_28);
lean_ctor_set(x_185, 3, x_51);
lean_ctor_set(x_185, 4, x_184);
lean_ctor_set(x_185, 5, x_174);
lean_ctor_set(x_185, 6, x_175);
lean_ctor_set(x_185, 7, x_176);
lean_ctor_set(x_185, 8, x_49);
lean_ctor_set(x_185, 9, x_177);
lean_ctor_set(x_185, 10, x_25);
lean_ctor_set(x_185, 11, x_178);
lean_ctor_set(x_185, 12, x_73);
lean_ctor_set_uint8(x_185, sizeof(void*)*13, x_180);
x_186 = lean_unbox(x_20);
lean_ctor_set_uint8(x_185, sizeof(void*)*13 + 1, x_186);
x_187 = l_Lean_PrettyPrinter_ppModule(x_172, x_185, x_181, x_182);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
x_191 = lean_st_ref_get(x_69, x_189);
lean_dec(x_69);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
x_194 = lean_unsigned_to_nat(120u);
x_195 = lean_format_pretty(x_188, x_194, x_51, x_51);
x_196 = lean_string_utf8_byte_size(x_195);
x_197 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_195, x_196, x_51);
x_198 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_195, x_197, x_196);
x_199 = lean_string_utf8_extract(x_195, x_197, x_198);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
x_200 = lean_mk_string_unchecked("\n", 1, 1);
x_201 = lean_string_append(x_199, x_200);
lean_dec(x_200);
if (lean_is_scalar(x_190)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_190;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_3);
if (lean_is_scalar(x_193)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_193;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_192);
return x_203;
}
else
{
lean_object* x_204; 
lean_dec(x_69);
x_204 = lean_ctor_get(x_187, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_205 = lean_ctor_get(x_187, 1);
lean_inc(x_205);
lean_dec(x_187);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_MessageData_toString(x_206, x_205);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_210, 0, x_208);
x_5 = x_210;
x_6 = x_209;
goto block_17;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_187, 1);
lean_inc(x_211);
lean_dec(x_187);
x_212 = lean_ctor_get(x_204, 0);
lean_inc(x_212);
lean_dec(x_204);
x_213 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_214 = l___private_Init_Data_Repr_0__Nat_reprFast(x_212);
x_215 = lean_string_append(x_213, x_214);
lean_dec(x_214);
x_216 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_5 = x_216;
x_6 = x_211;
goto block_17;
}
}
}
block_232:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_218 = lean_st_ref_take(x_69, x_168);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = l_Lean_Kernel_enableDiag(x_221, x_180);
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_219, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 5);
lean_inc(x_226);
x_227 = lean_ctor_get(x_219, 6);
lean_inc(x_227);
x_228 = lean_ctor_get(x_219, 7);
lean_inc(x_228);
lean_dec(x_219);
x_229 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_223);
lean_ctor_set(x_229, 2, x_224);
lean_ctor_set(x_229, 3, x_225);
lean_ctor_set(x_229, 4, x_62);
lean_ctor_set(x_229, 5, x_226);
lean_ctor_set(x_229, 6, x_227);
lean_ctor_set(x_229, 7, x_228);
x_230 = lean_st_ref_set(x_69, x_229, x_220);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
lean_inc(x_69);
x_181 = x_69;
x_182 = x_231;
goto block_217;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint64_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_330; uint8_t x_331; 
x_235 = lean_ctor_get(x_47, 0);
x_236 = lean_ctor_get(x_47, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_47);
x_237 = lean_unsigned_to_nat(0u);
x_238 = l_Lean_Name_mkStr1(x_34);
x_239 = lean_uint64_of_nat(x_237);
lean_inc(x_42);
x_240 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_240, 0, x_43);
lean_ctor_set(x_240, 1, x_42);
lean_ctor_set(x_240, 2, x_237);
lean_ctor_set(x_240, 3, x_237);
lean_ctor_set_usize(x_240, 4, x_37);
lean_inc(x_44);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_44);
lean_inc(x_42);
x_242 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_242, 0, x_45);
lean_ctor_set(x_242, 1, x_42);
lean_ctor_set(x_242, 2, x_237);
lean_ctor_set(x_242, 3, x_237);
lean_ctor_set_usize(x_242, 4, x_37);
x_243 = lean_box(0);
lean_inc(x_44);
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_44);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_44);
x_246 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_246, 0, x_46);
lean_ctor_set(x_246, 1, x_42);
lean_ctor_set(x_246, 2, x_237);
lean_ctor_set(x_246, 3, x_237);
lean_ctor_set_usize(x_246, 4, x_37);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_238);
lean_ctor_set(x_247, 1, x_25);
x_248 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_248, 0, x_240);
lean_ctor_set_uint64(x_248, sizeof(void*)*1, x_239);
lean_inc(x_241);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_241);
lean_ctor_set(x_249, 1, x_241);
lean_inc(x_242);
x_250 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set(x_250, 1, x_242);
lean_ctor_set(x_250, 2, x_243);
x_251 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_251, 0, x_244);
lean_ctor_set(x_251, 1, x_245);
lean_ctor_set(x_251, 2, x_246);
x_252 = lean_unbox(x_21);
lean_ctor_set_uint8(x_251, sizeof(void*)*3, x_252);
x_253 = lean_mk_empty_array_with_capacity(x_237);
lean_inc(x_249);
x_254 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_254, 0, x_32);
lean_ctor_set(x_254, 1, x_35);
lean_ctor_set(x_254, 2, x_247);
lean_ctor_set(x_254, 3, x_248);
lean_ctor_set(x_254, 4, x_249);
lean_ctor_set(x_254, 5, x_250);
lean_ctor_set(x_254, 6, x_251);
lean_ctor_set(x_254, 7, x_253);
x_255 = lean_st_mk_ref(x_254, x_236);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = l_Lean_inheritedTraceOptions;
x_259 = lean_st_ref_get(x_258, x_257);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_st_ref_get(x_256, x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_266 = l_Lake_Package_mkLeanConfig(x_1);
x_267 = lean_mk_string_unchecked("", 0, 0);
x_268 = l_Array_empty(lean_box(0));
x_269 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_266);
lean_inc(x_267);
if (lean_is_scalar(x_265)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_265;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_box(0);
x_272 = lean_box(0);
x_273 = lean_box(0);
x_274 = l_Lean_Core_getMaxHeartbeats(x_28);
x_275 = lean_box(0);
x_276 = l_Lean_diagnostics;
x_277 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_28, x_276);
x_330 = lean_ctor_get(x_263, 0);
lean_inc(x_330);
lean_dec(x_263);
x_331 = l_Lean_Kernel_isDiagnosticsEnabled(x_330);
lean_dec(x_330);
if (x_331 == 0)
{
if (x_277 == 0)
{
lean_dec(x_249);
lean_inc(x_256);
x_278 = x_256;
x_279 = x_264;
goto block_314;
}
else
{
goto block_329;
}
}
else
{
if (x_277 == 0)
{
goto block_329;
}
else
{
lean_dec(x_249);
lean_inc(x_256);
x_278 = x_256;
x_279 = x_264;
goto block_314;
}
}
block_314:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; 
x_280 = l_Lean_maxRecDepth;
x_281 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_28, x_280);
x_282 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_282, 0, x_267);
lean_ctor_set(x_282, 1, x_270);
lean_ctor_set(x_282, 2, x_28);
lean_ctor_set(x_282, 3, x_237);
lean_ctor_set(x_282, 4, x_281);
lean_ctor_set(x_282, 5, x_271);
lean_ctor_set(x_282, 6, x_272);
lean_ctor_set(x_282, 7, x_273);
lean_ctor_set(x_282, 8, x_235);
lean_ctor_set(x_282, 9, x_274);
lean_ctor_set(x_282, 10, x_25);
lean_ctor_set(x_282, 11, x_275);
lean_ctor_set(x_282, 12, x_260);
lean_ctor_set_uint8(x_282, sizeof(void*)*13, x_277);
x_283 = lean_unbox(x_20);
lean_ctor_set_uint8(x_282, sizeof(void*)*13 + 1, x_283);
x_284 = l_Lean_PrettyPrinter_ppModule(x_269, x_282, x_278, x_279);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
x_288 = lean_st_ref_get(x_256, x_286);
lean_dec(x_256);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
x_291 = lean_unsigned_to_nat(120u);
x_292 = lean_format_pretty(x_285, x_291, x_237, x_237);
x_293 = lean_string_utf8_byte_size(x_292);
x_294 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_292, x_293, x_237);
x_295 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_292, x_294, x_293);
x_296 = lean_string_utf8_extract(x_292, x_294, x_295);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_292);
x_297 = lean_mk_string_unchecked("\n", 1, 1);
x_298 = lean_string_append(x_296, x_297);
lean_dec(x_297);
if (lean_is_scalar(x_287)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_287;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_3);
if (lean_is_scalar(x_290)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_290;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_289);
return x_300;
}
else
{
lean_object* x_301; 
lean_dec(x_256);
x_301 = lean_ctor_get(x_284, 0);
lean_inc(x_301);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_302 = lean_ctor_get(x_284, 1);
lean_inc(x_302);
lean_dec(x_284);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = l_Lean_MessageData_toString(x_303, x_302);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_307, 0, x_305);
x_5 = x_307;
x_6 = x_306;
goto block_17;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_308 = lean_ctor_get(x_284, 1);
lean_inc(x_308);
lean_dec(x_284);
x_309 = lean_ctor_get(x_301, 0);
lean_inc(x_309);
lean_dec(x_301);
x_310 = lean_mk_string_unchecked("internal exception #", 20, 20);
x_311 = l___private_Init_Data_Repr_0__Nat_reprFast(x_309);
x_312 = lean_string_append(x_310, x_311);
lean_dec(x_311);
x_313 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_5 = x_313;
x_6 = x_308;
goto block_17;
}
}
}
block_329:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_315 = lean_st_ref_take(x_256, x_264);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
x_319 = l_Lean_Kernel_enableDiag(x_318, x_277);
x_320 = lean_ctor_get(x_316, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_316, 2);
lean_inc(x_321);
x_322 = lean_ctor_get(x_316, 3);
lean_inc(x_322);
x_323 = lean_ctor_get(x_316, 5);
lean_inc(x_323);
x_324 = lean_ctor_get(x_316, 6);
lean_inc(x_324);
x_325 = lean_ctor_get(x_316, 7);
lean_inc(x_325);
lean_dec(x_316);
x_326 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_326, 0, x_319);
lean_ctor_set(x_326, 1, x_320);
lean_ctor_set(x_326, 2, x_321);
lean_ctor_set(x_326, 3, x_322);
lean_ctor_set(x_326, 4, x_249);
lean_ctor_set(x_326, 5, x_323);
lean_ctor_set(x_326, 6, x_324);
lean_ctor_set(x_326, 7, x_325);
x_327 = lean_st_ref_set(x_256, x_326, x_317);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
lean_inc(x_256);
x_278 = x_256;
x_279 = x_328;
goto block_314;
}
}
}
else
{
uint8_t x_332; 
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_31);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_333 = lean_ctor_get(x_31, 0);
x_334 = lean_io_error_to_string(x_333);
x_335 = lean_box(3);
x_336 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_336, 0, x_334);
x_337 = lean_unbox(x_335);
lean_ctor_set_uint8(x_336, sizeof(void*)*1, x_337);
x_338 = lean_array_get_size(x_3);
x_339 = lean_array_push(x_3, x_336);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 0, x_340);
return x_31;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_341 = lean_ctor_get(x_31, 0);
x_342 = lean_ctor_get(x_31, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_31);
x_343 = lean_io_error_to_string(x_341);
x_344 = lean_box(3);
x_345 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_345, 0, x_343);
x_346 = lean_unbox(x_344);
lean_ctor_set_uint8(x_345, sizeof(void*)*1, x_346);
x_347 = lean_array_get_size(x_3);
x_348 = lean_array_push(x_3, x_345);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_342);
return x_350;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_351 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
x_352 = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), x_351);
lean_dec(x_351);
x_353 = l_Lake_Package_mkTomlConfig(x_1, x_352);
x_354 = l_Lake_Toml_ppTable(x_353);
lean_dec(x_353);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_3);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_4);
return x_356;
}
block_17:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_mk_string_unchecked("(internal) failed to pretty print Lean configuration: ", 54, 54);
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_box(3);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_array_get_size(x_3);
x_14 = lean_array_push(x_3, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_Package_mkConfigString(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lake_Config_Lang(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Translate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Lang(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Toml(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
