// Lean compiler output
// Module: Lake.Load.Materialize
// Imports: Lake.Util.Git Lake.Load.Manifest Lake.Config.Dependency Lake.Config.Package Lake.Reservoir
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
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize_mkDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object*);
lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object*);
lean_object* l_Lake_testProc(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_fetchPkg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__2(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object*);
lean_object* l_Lake_RegistryPkg_gitSrc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__2___boxed(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_4_(lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedMaterializedDep;
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("origin", 6, 6);
lean_inc(x_2);
x_7 = l_Lake_GitRepo_findRemoteRevision(x_2, x_3, x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_2);
x_12 = l_Lake_GitRepo_getHeadRevision(x_2, x_11, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_string_dec_eq(x_16, x_10);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; 
lean_free_object(x_13);
x_19 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
x_20 = lean_string_append(x_1, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_10);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_array_push(x_17, x_25);
x_28 = lean_mk_string_unchecked("checkout", 8, 8);
x_29 = lean_mk_string_unchecked("--detach", 8, 8);
x_30 = lean_mk_string_unchecked("--", 2, 2);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
x_33 = lean_array_push(x_32, x_28);
x_34 = lean_array_push(x_33, x_29);
x_35 = lean_array_push(x_34, x_10);
x_36 = lean_array_push(x_35, x_30);
x_37 = lean_box(1);
x_38 = lean_alloc_ctor(0, 0, 3);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, 0, x_39);
x_40 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, 1, x_40);
x_41 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, 2, x_41);
x_42 = lean_mk_string_unchecked("git", 3, 3);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_2);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_mk_empty_array_with_capacity(x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set(x_47, 4, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*5, x_48);
lean_ctor_set_uint8(x_47, sizeof(void*)*5 + 1, x_18);
x_49 = lean_unbox(x_46);
x_50 = l_Lake_proc(x_47, x_49, x_27, x_14);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_10);
x_51 = lean_mk_string_unchecked("diff", 4, 4);
x_52 = lean_mk_string_unchecked("--exit-code", 11, 11);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_mk_empty_array_with_capacity(x_53);
x_55 = lean_array_push(x_54, x_51);
x_56 = lean_array_push(x_55, x_52);
x_57 = lean_box(1);
x_58 = lean_alloc_ctor(0, 0, 3);
x_59 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, 0, x_59);
x_60 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, 1, x_60);
x_61 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, 2, x_61);
x_62 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_2);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_2);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_mk_empty_array_with_capacity(x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_56);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*5, x_18);
x_68 = lean_unbox(x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*5 + 1, x_68);
x_69 = l_Lake_testProc(x_67, x_14);
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_69, 0);
lean_dec(x_73);
x_74 = lean_mk_string_unchecked(": repository '", 14, 14);
x_75 = lean_string_append(x_1, x_74);
lean_dec(x_74);
x_76 = lean_string_append(x_75, x_2);
lean_dec(x_2);
x_77 = lean_mk_string_unchecked("' has local changes", 19, 19);
x_78 = lean_string_append(x_76, x_77);
lean_dec(x_77);
x_79 = lean_box(2);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
x_82 = lean_box(0);
x_83 = lean_array_push(x_17, x_80);
lean_ctor_set(x_13, 1, x_83);
lean_ctor_set(x_13, 0, x_82);
lean_ctor_set(x_69, 0, x_13);
return x_69;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_ctor_get(x_69, 1);
lean_inc(x_84);
lean_dec(x_69);
x_85 = lean_mk_string_unchecked(": repository '", 14, 14);
x_86 = lean_string_append(x_1, x_85);
lean_dec(x_85);
x_87 = lean_string_append(x_86, x_2);
lean_dec(x_2);
x_88 = lean_mk_string_unchecked("' has local changes", 19, 19);
x_89 = lean_string_append(x_87, x_88);
lean_dec(x_88);
x_90 = lean_box(2);
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_92);
x_93 = lean_box(0);
x_94 = lean_array_push(x_17, x_91);
lean_ctor_set(x_13, 1, x_94);
lean_ctor_set(x_13, 0, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_13);
lean_ctor_set(x_95, 1, x_84);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_69);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_69, 0);
lean_dec(x_97);
x_98 = lean_box(0);
lean_ctor_set(x_13, 0, x_98);
lean_ctor_set(x_69, 0, x_13);
return x_69;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_69, 1);
lean_inc(x_99);
lean_dec(x_69);
x_100 = lean_box(0);
lean_ctor_set(x_13, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_13);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_13, 0);
x_103 = lean_ctor_get(x_13, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_13);
x_104 = lean_string_dec_eq(x_102, x_10);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; 
x_105 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
x_106 = lean_string_append(x_1, x_105);
lean_dec(x_105);
x_107 = lean_string_append(x_106, x_10);
x_108 = lean_mk_string_unchecked("'", 1, 1);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_box(1);
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
x_112 = lean_unbox(x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_112);
x_113 = lean_array_push(x_103, x_111);
x_114 = lean_mk_string_unchecked("checkout", 8, 8);
x_115 = lean_mk_string_unchecked("--detach", 8, 8);
x_116 = lean_mk_string_unchecked("--", 2, 2);
x_117 = lean_unsigned_to_nat(4u);
x_118 = lean_mk_empty_array_with_capacity(x_117);
x_119 = lean_array_push(x_118, x_114);
x_120 = lean_array_push(x_119, x_115);
x_121 = lean_array_push(x_120, x_10);
x_122 = lean_array_push(x_121, x_116);
x_123 = lean_box(1);
x_124 = lean_alloc_ctor(0, 0, 3);
x_125 = lean_unbox(x_123);
lean_ctor_set_uint8(x_124, 0, x_125);
x_126 = lean_unbox(x_123);
lean_ctor_set_uint8(x_124, 1, x_126);
x_127 = lean_unbox(x_123);
lean_ctor_set_uint8(x_124, 2, x_127);
x_128 = lean_mk_string_unchecked("git", 3, 3);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_2);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_mk_empty_array_with_capacity(x_130);
x_132 = lean_box(1);
x_133 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_128);
lean_ctor_set(x_133, 2, x_122);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_131);
x_134 = lean_unbox(x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*5, x_134);
lean_ctor_set_uint8(x_133, sizeof(void*)*5 + 1, x_104);
x_135 = lean_unbox(x_132);
x_136 = l_Lake_proc(x_133, x_135, x_113, x_14);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_10);
x_137 = lean_mk_string_unchecked("diff", 4, 4);
x_138 = lean_mk_string_unchecked("--exit-code", 11, 11);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_mk_empty_array_with_capacity(x_139);
x_141 = lean_array_push(x_140, x_137);
x_142 = lean_array_push(x_141, x_138);
x_143 = lean_box(1);
x_144 = lean_alloc_ctor(0, 0, 3);
x_145 = lean_unbox(x_143);
lean_ctor_set_uint8(x_144, 0, x_145);
x_146 = lean_unbox(x_143);
lean_ctor_set_uint8(x_144, 1, x_146);
x_147 = lean_unbox(x_143);
lean_ctor_set_uint8(x_144, 2, x_147);
x_148 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_2);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_2);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_mk_empty_array_with_capacity(x_150);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_148);
lean_ctor_set(x_153, 2, x_142);
lean_ctor_set(x_153, 3, x_149);
lean_ctor_set(x_153, 4, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*5, x_104);
x_154 = lean_unbox(x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*5 + 1, x_154);
x_155 = l_Lake_testProc(x_153, x_14);
lean_dec(x_153);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
x_160 = lean_mk_string_unchecked(": repository '", 14, 14);
x_161 = lean_string_append(x_1, x_160);
lean_dec(x_160);
x_162 = lean_string_append(x_161, x_2);
lean_dec(x_2);
x_163 = lean_mk_string_unchecked("' has local changes", 19, 19);
x_164 = lean_string_append(x_162, x_163);
lean_dec(x_163);
x_165 = lean_box(2);
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_164);
x_167 = lean_unbox(x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_167);
x_168 = lean_box(0);
x_169 = lean_array_push(x_103, x_166);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
if (lean_is_scalar(x_159)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_159;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_158);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_173 = x_155;
} else {
 lean_dec_ref(x_155);
 x_173 = lean_box(0);
}
x_174 = lean_box(0);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_103);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
return x_176;
}
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_12);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_12, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_13);
if (x_179 == 0)
{
return x_12;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_13, 0);
x_181 = lean_ctor_get(x_13, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_13);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_12, 0, x_182);
return x_12;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_183 = lean_ctor_get(x_12, 1);
lean_inc(x_183);
lean_dec(x_12);
x_184 = lean_ctor_get(x_13, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_13, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_186 = x_13;
} else {
 lean_dec_ref(x_13);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_183);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_7);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_7, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_8);
if (x_191 == 0)
{
return x_7;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_8, 0);
x_193 = lean_ctor_get(x_8, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_8);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set(x_7, 0, x_194);
return x_7;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_7, 1);
lean_inc(x_195);
lean_dec(x_7);
x_196 = lean_ctor_get(x_8, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_8, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_198 = x_8;
} else {
 lean_dec_ref(x_8);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_195);
return x_200;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_cloneGitPkg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_7 = lean_mk_string_unchecked(": cloning ", 10, 10);
lean_inc(x_1);
x_8 = lean_string_append(x_1, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_8, x_3);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_array_push(x_5, x_11);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 0, 3);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 0, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 1, x_17);
x_18 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, 2, x_18);
x_19 = lean_mk_string_unchecked("git", 3, 3);
x_20 = lean_mk_string_unchecked("clone", 5, 5);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_array_push(x_22, x_20);
x_24 = lean_array_push(x_23, x_3);
lean_inc(x_2);
x_25 = lean_array_push(x_24, x_2);
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
x_29 = lean_box(1);
x_30 = lean_box(0);
lean_inc(x_28);
lean_inc(x_19);
lean_inc(x_15);
x_31 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_28);
x_32 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_32);
x_33 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*5 + 1, x_33);
x_34 = lean_unbox(x_29);
x_35 = l_Lake_proc(x_31, x_34, x_13, x_6);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_37; 
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_36, 0, x_41);
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_47 = x_36;
} else {
 lean_dec_ref(x_36);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_dec(x_35);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
lean_dec(x_36);
x_53 = !lean_is_exclusive(x_4);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_mk_string_unchecked("origin", 6, 6);
lean_inc(x_2);
x_56 = l_Lake_GitRepo_resolveRemoteRevision(x_54, x_55, x_2, x_52, x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
x_62 = lean_string_append(x_1, x_61);
lean_dec(x_61);
x_63 = lean_string_append(x_62, x_59);
x_64 = lean_mk_string_unchecked("'", 1, 1);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_unbox(x_10);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_67);
x_68 = lean_array_push(x_60, x_66);
x_69 = lean_mk_string_unchecked("checkout", 8, 8);
x_70 = lean_mk_string_unchecked("--detach", 8, 8);
x_71 = lean_mk_string_unchecked("--", 2, 2);
x_72 = lean_unsigned_to_nat(4u);
x_73 = lean_mk_empty_array_with_capacity(x_72);
x_74 = lean_array_push(x_73, x_69);
x_75 = lean_array_push(x_74, x_70);
x_76 = lean_array_push(x_75, x_59);
x_77 = lean_array_push(x_76, x_71);
lean_ctor_set(x_4, 0, x_2);
x_78 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_78, 0, x_15);
lean_ctor_set(x_78, 1, x_19);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_78, 3, x_4);
lean_ctor_set(x_78, 4, x_28);
x_79 = lean_unbox(x_29);
lean_ctor_set_uint8(x_78, sizeof(void*)*5, x_79);
x_80 = lean_unbox(x_30);
lean_ctor_set_uint8(x_78, sizeof(void*)*5 + 1, x_80);
x_81 = lean_unbox(x_29);
x_82 = l_Lake_proc(x_78, x_81, x_68, x_58);
return x_82;
}
else
{
uint8_t x_83; 
lean_free_object(x_4);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_56);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_56, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_57);
if (x_85 == 0)
{
return x_56;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_57, 0);
x_87 = lean_ctor_get(x_57, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_56, 0, x_88);
return x_56;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_56, 1);
lean_inc(x_89);
lean_dec(x_56);
x_90 = lean_ctor_get(x_57, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_57, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_92 = x_57;
} else {
 lean_dec_ref(x_57);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_4, 0);
lean_inc(x_95);
lean_dec(x_4);
x_96 = lean_mk_string_unchecked("origin", 6, 6);
lean_inc(x_2);
x_97 = l_Lake_GitRepo_resolveRemoteRevision(x_95, x_96, x_2, x_52, x_51);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_mk_string_unchecked(": checking out revision '", 25, 25);
x_103 = lean_string_append(x_1, x_102);
lean_dec(x_102);
x_104 = lean_string_append(x_103, x_100);
x_105 = lean_mk_string_unchecked("'", 1, 1);
x_106 = lean_string_append(x_104, x_105);
lean_dec(x_105);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_unbox(x_10);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
x_109 = lean_array_push(x_101, x_107);
x_110 = lean_mk_string_unchecked("checkout", 8, 8);
x_111 = lean_mk_string_unchecked("--detach", 8, 8);
x_112 = lean_mk_string_unchecked("--", 2, 2);
x_113 = lean_unsigned_to_nat(4u);
x_114 = lean_mk_empty_array_with_capacity(x_113);
x_115 = lean_array_push(x_114, x_110);
x_116 = lean_array_push(x_115, x_111);
x_117 = lean_array_push(x_116, x_100);
x_118 = lean_array_push(x_117, x_112);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_2);
x_120 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_120, 0, x_15);
lean_ctor_set(x_120, 1, x_19);
lean_ctor_set(x_120, 2, x_118);
lean_ctor_set(x_120, 3, x_119);
lean_ctor_set(x_120, 4, x_28);
x_121 = lean_unbox(x_29);
lean_ctor_set_uint8(x_120, sizeof(void*)*5, x_121);
x_122 = lean_unbox(x_30);
lean_ctor_set_uint8(x_120, sizeof(void*)*5 + 1, x_122);
x_123 = lean_unbox(x_29);
x_124 = l_Lake_proc(x_120, x_123, x_109, x_99);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_ctor_get(x_97, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_126 = x_97;
} else {
 lean_dec_ref(x_97);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_98, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_98, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_129 = x_98;
} else {
 lean_dec_ref(x_98);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_125);
return x_131;
}
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_53 = lean_mk_string_unchecked("origin", 6, 6);
x_54 = lean_mk_string_unchecked("remote", 6, 6);
x_55 = lean_mk_string_unchecked("get-url", 7, 7);
x_56 = lean_unsigned_to_nat(3u);
x_57 = lean_mk_empty_array_with_capacity(x_56);
x_58 = lean_array_push(x_57, x_54);
x_59 = lean_array_push(x_58, x_55);
x_60 = lean_array_push(x_59, x_53);
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(0, 0, 3);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, 0, x_63);
x_64 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, 1, x_64);
x_65 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, 2, x_65);
x_66 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_2);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_2);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_mk_empty_array_with_capacity(x_68);
x_70 = lean_box(1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_66);
lean_ctor_set(x_72, 2, x_60);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set(x_72, 4, x_69);
x_73 = lean_unbox(x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*5, x_73);
x_74 = lean_unbox(x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 1, x_74);
x_75 = l_Lake_captureProc_x3f(x_72, x_6);
lean_dec(x_72);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_7 = x_77;
goto block_52;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_string_dec_eq(x_79, x_3);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_io_realpath(x_79, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_3);
x_84 = lean_io_realpath(x_3, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_string_dec_eq(x_82, x_85);
lean_dec(x_85);
lean_dec(x_82);
if (x_87 == 0)
{
x_7 = x_86;
goto block_52;
}
else
{
lean_object* x_88; 
lean_dec(x_3);
x_88 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_5, x_86);
return x_88;
}
}
else
{
lean_object* x_89; 
lean_dec(x_82);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_7 = x_89;
goto block_52;
}
}
else
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_7 = x_90;
goto block_52;
}
}
else
{
lean_object* x_91; 
lean_dec(x_79);
lean_dec(x_3);
x_91 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_5, x_78);
return x_91;
}
}
block_52:
{
uint8_t x_8; 
x_8 = l_System_Platform_isWindows;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_mk_string_unchecked(": URL has changed; deleting '", 29, 29);
lean_inc(x_1);
x_10 = lean_string_append(x_1, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_2);
x_12 = lean_mk_string_unchecked("' and cloning again", 19, 19);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_IO_FS_removeDirAll(x_2, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_push(x_5, x_15);
x_20 = l_Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_19, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_array_push(x_5, x_15);
x_24 = lean_io_error_to_string(x_22);
x_25 = lean_box(3);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_array_get_size(x_23);
x_29 = lean_array_push(x_23, x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_array_push(x_5, x_15);
x_34 = lean_io_error_to_string(x_31);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_array_get_size(x_33);
x_39 = lean_array_push(x_33, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
x_42 = lean_mk_string_unchecked(": URL has changed; you might need to delete '", 45, 45);
lean_inc(x_1);
x_43 = lean_string_append(x_1, x_42);
lean_dec(x_42);
x_44 = lean_string_append(x_43, x_2);
x_45 = lean_mk_string_unchecked("' manually", 10, 10);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = lean_box(1);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_array_push(x_5, x_48);
x_51 = l_Lake_updateGitPkg(x_1, x_2, x_4, x_50, x_7);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_materializeGitRepo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_System_FilePath_isDir(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lake_cloneGitPkg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lake_updateGitRepo(x_1, x_2, x_3, x_4, x_5, x_12);
return x_13;
}
}
}
static lean_object* _init_l_Lake_instInhabitedMaterializedDep() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
lean_inc_n(x_1, 2);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_7);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_name(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_scope___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_scope(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_manifestFile_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_manifestFile_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MaterializedDep_configFile___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_MaterializedDep_configFile(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_27; 
x_27 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_27);
x_4 = x_27;
x_5 = x_27;
goto block_26;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_mk_string_unchecked(" @ ", 3, 3);
x_31 = l_String_quote(x_29);
lean_dec(x_29);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_31);
x_32 = lean_unsigned_to_nat(120u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_format_pretty(x_3, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
x_36 = lean_mk_string_unchecked("\n    rev = ", 11, 11);
x_37 = lean_string_append(x_36, x_34);
lean_dec(x_34);
x_4 = x_35;
x_5 = x_37;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_3, 0);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_mk_string_unchecked(" @ ", 3, 3);
x_40 = l_String_quote(x_38);
lean_dec(x_38);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_unsigned_to_nat(120u);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_format_pretty(x_41, x_42, x_43, x_43);
x_45 = lean_string_append(x_39, x_44);
x_46 = lean_mk_string_unchecked("\n    rev = ", 11, 11);
x_47 = lean_string_append(x_46, x_44);
lean_dec(x_44);
x_4 = x_45;
x_5 = x_47;
goto block_26;
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_mk_string_unchecked("/", 1, 1);
lean_inc(x_1);
x_7 = lean_string_append(x_1, x_6);
x_8 = lean_string_append(x_7, x_2);
x_9 = lean_mk_string_unchecked(": package not found on Reservoir.\n\n  If the package is on GitHub, you can add a Git source. For example:\n\n    require ...\n      from git \"https://github.com/", 157, 157);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_1);
x_12 = lean_string_append(x_11, x_6);
x_13 = lean_string_append(x_12, x_2);
x_14 = lean_mk_string_unchecked("\"", 1, 1);
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_4);
lean_dec(x_4);
x_17 = lean_mk_string_unchecked("\n\n  or, if using TOML:\n\n    [[require]]\n    git = \"https://github.com/", 70, 70);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec(x_1);
x_20 = lean_string_append(x_19, x_6);
lean_dec(x_6);
x_21 = lean_string_append(x_20, x_2);
x_22 = lean_string_append(x_21, x_14);
lean_dec(x_14);
x_23 = lean_string_append(x_22, x_5);
lean_dec(x_5);
x_24 = lean_mk_string_unchecked("\n    ...\n", 9, 9);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_pkgNotIndexed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_pkgNotIndexed(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lake_defaultConfigFile;
x_9 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_mkDep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_Dependency_materialize_mkDep(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_28; lean_object* x_29; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_28 = l_Lake_joinRelative(x_4, x_6);
x_69 = lean_ctor_get(x_3, 5);
x_70 = lean_ctor_get(x_1, 0);
x_71 = l_Lean_NameMap_find_x3f(lean_box(0), x_69, x_70);
if (lean_obj_tag(x_71) == 0)
{
x_29 = x_7;
goto block_68;
}
else
{
lean_object* x_72; 
lean_dec(x_7);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_29 = x_72;
goto block_68;
}
block_27:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set(x_18, 3, x_10);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = l_Lake_defaultConfigFile;
x_22 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_2);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_8);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
return x_26;
}
block_68:
{
lean_object* x_30; lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_29);
lean_inc(x_28);
x_30 = l_Lake_materializeGitRepo(x_5, x_28, x_29, x_9, x_11, x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lake_GitRepo_getHeadRevision(x_28, x_33, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_13 = x_38;
x_14 = x_29;
x_15 = x_37;
x_16 = x_36;
x_17 = x_6;
goto block_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = l_Lake_joinRelative(x_6, x_42);
lean_dec(x_42);
x_13 = x_41;
x_14 = x_29;
x_15 = x_40;
x_16 = x_39;
x_17 = x_43;
goto block_27;
}
}
else
{
uint8_t x_44; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_34, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_34, 0, x_49);
return x_34;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = lean_ctor_get(x_35, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_53 = x_35;
} else {
 lean_dec_ref(x_35);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_30);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_30, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
return x_30;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_31, 0);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_31);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_30, 0, x_61);
return x_30;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_dec(x_30);
x_63 = lean_ctor_get(x_31, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_65 = x_31;
} else {
 lean_dec_ref(x_31);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize_materializeGit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lake_Dependency_materialize_materializeGit(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Dependency_materialize___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_6);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_string_utf8_byte_size(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_instDecidableEqPos(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_136; 
x_40 = lean_box(x_39);
x_41 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__0___boxed), 2, 1);
lean_closure_set(x_41, 0, x_40);
x_136 = lean_ctor_get(x_1, 2);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
x_42 = x_136;
x_43 = x_7;
x_44 = x_8;
goto block_135;
}
else
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_mk_string_unchecked("git#", 4, 4);
x_140 = lean_string_utf8_byte_size(x_138);
lean_inc(x_140);
lean_inc(x_138);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_38);
lean_ctor_set(x_141, 2, x_140);
x_142 = lean_unsigned_to_nat(4u);
x_143 = l_Substring_nextn(x_141, x_142, x_38);
lean_dec(x_141);
lean_inc(x_143);
lean_inc(x_138);
x_144 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_38);
lean_ctor_set(x_144, 2, x_143);
x_145 = lean_string_utf8_byte_size(x_139);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_38);
lean_ctor_set(x_146, 2, x_145);
x_147 = l_Substring_beq(x_144, x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_143);
lean_dec(x_140);
lean_free_object(x_136);
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_1, 0);
lean_inc(x_148);
lean_dec(x_1);
x_149 = lean_box(1);
x_150 = lean_unbox(x_149);
x_151 = l_Lean_Name_toString(x_148, x_150, x_41);
x_152 = lean_mk_string_unchecked(": unsupported dependency version format '", 41, 41);
x_153 = lean_string_append(x_151, x_152);
lean_dec(x_152);
x_154 = lean_string_append(x_153, x_138);
lean_dec(x_138);
x_155 = lean_mk_string_unchecked("' (should be \"git#<rev>\")", 25, 25);
x_156 = lean_string_append(x_154, x_155);
lean_dec(x_155);
x_157 = lean_box(3);
x_158 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_158, 0, x_156);
x_159 = lean_unbox(x_157);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_159);
x_160 = lean_array_get_size(x_7);
x_161 = lean_array_push(x_7, x_158);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_8);
return x_163;
}
else
{
lean_object* x_164; 
x_164 = lean_string_utf8_extract(x_138, x_143, x_140);
lean_dec(x_140);
lean_dec(x_143);
lean_dec(x_138);
lean_ctor_set(x_136, 0, x_164);
x_42 = x_136;
x_43 = x_7;
x_44 = x_8;
goto block_135;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_165 = lean_ctor_get(x_136, 0);
lean_inc(x_165);
lean_dec(x_136);
x_166 = lean_mk_string_unchecked("git#", 4, 4);
x_167 = lean_string_utf8_byte_size(x_165);
lean_inc(x_167);
lean_inc(x_165);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_38);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_unsigned_to_nat(4u);
x_170 = l_Substring_nextn(x_168, x_169, x_38);
lean_dec(x_168);
lean_inc(x_170);
lean_inc(x_165);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_38);
lean_ctor_set(x_171, 2, x_170);
x_172 = lean_string_utf8_byte_size(x_166);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_166);
lean_ctor_set(x_173, 1, x_38);
lean_ctor_set(x_173, 2, x_172);
x_174 = l_Substring_beq(x_171, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_170);
lean_dec(x_167);
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_175 = lean_ctor_get(x_1, 0);
lean_inc(x_175);
lean_dec(x_1);
x_176 = lean_box(1);
x_177 = lean_unbox(x_176);
x_178 = l_Lean_Name_toString(x_175, x_177, x_41);
x_179 = lean_mk_string_unchecked(": unsupported dependency version format '", 41, 41);
x_180 = lean_string_append(x_178, x_179);
lean_dec(x_179);
x_181 = lean_string_append(x_180, x_165);
lean_dec(x_165);
x_182 = lean_mk_string_unchecked("' (should be \"git#<rev>\")", 25, 25);
x_183 = lean_string_append(x_181, x_182);
lean_dec(x_182);
x_184 = lean_box(3);
x_185 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_185, 0, x_183);
x_186 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_186);
x_187 = lean_array_get_size(x_7);
x_188 = lean_array_push(x_7, x_185);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_8);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_string_utf8_extract(x_165, x_170, x_167);
lean_dec(x_167);
lean_dec(x_170);
lean_dec(x_165);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_42 = x_192;
x_43 = x_7;
x_44 = x_8;
goto block_135;
}
}
}
block_135:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = l_Lean_Name_toString(x_45, x_39, x_41);
lean_inc(x_36);
lean_inc(x_3);
x_47 = l_Lake_Reservoir_fetchPkg_x3f(x_3, x_36, x_46, x_43, x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = l_Lake_pkgNotIndexed(x_36, x_46, x_42);
lean_dec(x_46);
x_56 = lean_box(3);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_unbox(x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
x_59 = lean_array_get_size(x_53);
x_60 = lean_array_push(x_53, x_57);
lean_ctor_set_tag(x_48, 1);
lean_ctor_set(x_48, 1, x_60);
lean_ctor_set(x_48, 0, x_59);
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_dec(x_48);
x_62 = l_Lake_pkgNotIndexed(x_36, x_46, x_42);
lean_dec(x_46);
x_63 = lean_box(3);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_array_get_size(x_61);
x_67 = lean_array_push(x_61, x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_47, 0, x_68);
return x_47;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_47, 1);
lean_inc(x_69);
lean_dec(x_47);
x_70 = lean_ctor_get(x_48, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_71 = x_48;
} else {
 lean_dec_ref(x_48);
 x_71 = lean_box(0);
}
x_72 = l_Lake_pkgNotIndexed(x_36, x_46, x_42);
lean_dec(x_46);
x_73 = lean_box(3);
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_unbox(x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_75);
x_76 = lean_array_get_size(x_70);
x_77 = lean_array_push(x_70, x_74);
if (lean_is_scalar(x_71)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_71;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_46);
lean_dec(x_36);
x_80 = lean_ctor_get(x_47, 1);
lean_inc(x_80);
lean_dec(x_47);
x_81 = lean_ctor_get(x_48, 1);
lean_inc(x_81);
lean_dec(x_48);
x_82 = lean_ctor_get(x_49, 0);
lean_inc(x_82);
lean_dec(x_49);
x_83 = l_Lake_RegistryPkg_gitSrc_x3f(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = x_82;
x_22 = x_81;
x_23 = x_80;
goto block_34;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 4);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = l_Lake_joinRelative(x_5, x_89);
lean_dec(x_89);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_92 = lean_mk_string_unchecked("", 0, 0);
x_9 = x_87;
x_10 = x_42;
x_11 = x_80;
x_12 = x_91;
x_13 = x_81;
x_14 = x_85;
x_15 = x_88;
x_16 = x_90;
x_17 = x_92;
goto block_20;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_dec(x_82);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
x_9 = x_87;
x_10 = x_42;
x_11 = x_80;
x_12 = x_93;
x_13 = x_81;
x_14 = x_85;
x_15 = x_88;
x_16 = x_90;
x_17 = x_94;
goto block_20;
}
}
else
{
lean_dec(x_84);
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = x_82;
x_22 = x_81;
x_23 = x_80;
goto block_34;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_47);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_47, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_48);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_48, 1);
x_99 = lean_mk_string_unchecked("/", 1, 1);
x_100 = lean_string_append(x_36, x_99);
lean_dec(x_99);
x_101 = lean_string_append(x_100, x_46);
lean_dec(x_46);
x_102 = lean_mk_string_unchecked(": could not materialize package: this may be a transient error or a bug in Lake or Reservoir", 92, 92);
x_103 = lean_string_append(x_101, x_102);
lean_dec(x_102);
x_104 = lean_box(3);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
x_106 = lean_unbox(x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_106);
x_107 = lean_array_push(x_98, x_105);
lean_ctor_set(x_48, 1, x_107);
return x_47;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_48, 0);
x_109 = lean_ctor_get(x_48, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_48);
x_110 = lean_mk_string_unchecked("/", 1, 1);
x_111 = lean_string_append(x_36, x_110);
lean_dec(x_110);
x_112 = lean_string_append(x_111, x_46);
lean_dec(x_46);
x_113 = lean_mk_string_unchecked(": could not materialize package: this may be a transient error or a bug in Lake or Reservoir", 92, 92);
x_114 = lean_string_append(x_112, x_113);
lean_dec(x_113);
x_115 = lean_box(3);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
x_117 = lean_unbox(x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_117);
x_118 = lean_array_push(x_109, x_116);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_47, 0, x_119);
return x_47;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get(x_47, 1);
lean_inc(x_120);
lean_dec(x_47);
x_121 = lean_ctor_get(x_48, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_48, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_123 = x_48;
} else {
 lean_dec_ref(x_48);
 x_123 = lean_box(0);
}
x_124 = lean_mk_string_unchecked("/", 1, 1);
x_125 = lean_string_append(x_36, x_124);
lean_dec(x_124);
x_126 = lean_string_append(x_125, x_46);
lean_dec(x_46);
x_127 = lean_mk_string_unchecked(": could not materialize package: this may be a transient error or a bug in Lake or Reservoir", 92, 92);
x_128 = lean_string_append(x_126, x_127);
lean_dec(x_127);
x_129 = lean_box(3);
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_128);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_131);
x_132 = lean_array_push(x_122, x_130);
if (lean_is_scalar(x_123)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_123;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_120);
return x_134;
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__2___boxed), 1, 0);
x_194 = lean_ctor_get(x_1, 0);
lean_inc(x_194);
lean_dec(x_1);
x_195 = l_Lean_Name_toString(x_194, x_39, x_193);
x_196 = lean_mk_string_unchecked(": ill-formed dependency: dependency is missing a source and is missing a scope for Reservoir", 92, 92);
x_197 = lean_string_append(x_195, x_196);
lean_dec(x_196);
x_198 = lean_box(3);
x_199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_199, 0, x_197);
x_200 = lean_unbox(x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_200);
x_201 = lean_array_get_size(x_7);
x_202 = lean_array_push(x_7, x_199);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
else
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_35, 0);
lean_inc(x_205);
lean_dec(x_35);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = l_Lake_joinRelative(x_6, x_207);
lean_dec(x_207);
x_209 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_208);
lean_ctor_set(x_205, 0, x_208);
x_210 = lean_ctor_get(x_1, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_1, 1);
lean_inc(x_211);
lean_dec(x_1);
x_212 = l_Lake_defaultConfigFile;
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_214, 0, x_210);
lean_ctor_set(x_214, 1, x_211);
lean_ctor_set(x_214, 2, x_212);
lean_ctor_set(x_214, 3, x_213);
lean_ctor_set(x_214, 4, x_205);
lean_ctor_set_uint8(x_214, sizeof(void*)*5, x_2);
x_215 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set(x_215, 1, x_209);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_7);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_8);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_218 = lean_ctor_get(x_205, 0);
lean_inc(x_218);
lean_dec(x_205);
x_219 = l_Lake_joinRelative(x_6, x_218);
lean_dec(x_218);
x_220 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_219);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_219);
x_222 = lean_ctor_get(x_1, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_1, 1);
lean_inc(x_223);
lean_dec(x_1);
x_224 = l_Lake_defaultConfigFile;
x_225 = lean_box(0);
x_226 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_223);
lean_ctor_set(x_226, 2, x_224);
lean_ctor_set(x_226, 3, x_225);
lean_ctor_set(x_226, 4, x_221);
lean_ctor_set_uint8(x_226, sizeof(void*)*5, x_2);
x_227 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_220);
lean_ctor_set(x_227, 2, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_7);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_8);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_242; 
lean_dec(x_6);
x_230 = lean_ctor_get(x_205, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_205, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_205, 2);
lean_inc(x_232);
lean_dec(x_205);
x_233 = lean_ctor_get(x_1, 0);
lean_inc(x_233);
x_234 = lean_box(0);
x_235 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__0___boxed), 2, 1);
lean_closure_set(x_235, 0, x_234);
x_236 = lean_unbox(x_234);
x_237 = l_Lean_Name_toString(x_233, x_236, x_235);
lean_inc(x_230);
x_242 = l_Lake_Git_filterUrl_x3f(x_230);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_mk_string_unchecked("", 0, 0);
x_238 = x_243;
goto block_241;
}
else
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
lean_dec(x_242);
x_238 = x_244;
goto block_241;
}
block_241:
{
lean_object* x_239; lean_object* x_240; 
x_239 = l_Lake_joinRelative(x_5, x_237);
x_240 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_237, x_239, x_230, x_238, x_231, x_232, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_240;
}
}
}
block_20:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_18; 
x_18 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_12, x_16, x_14, x_17, x_9, x_15, x_13, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_9);
x_19 = l_Lake_Dependency_materialize_materializeGit(x_1, x_2, x_3, x_4, x_12, x_16, x_14, x_17, x_10, x_15, x_13, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_19;
}
}
block_34:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_mk_string_unchecked(": Git source not found on Reservoir", 35, 35);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_box(3);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_array_get_size(x_22);
x_31 = lean_array_push(x_22, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Dependency_materialize___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___lam__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Dependency_materialize___lam__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lake_Dependency_materialize(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize_mkDep(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("", 0, 0);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_65; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 3);
lean_inc(x_23);
lean_dec(x_15);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_box(0);
x_33 = lean_alloc_closure((void*)(l_Lake_Dependency_materialize___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_unbox(x_32);
lean_inc(x_31);
x_35 = l_Lean_Name_toString(x_31, x_34, x_33);
x_36 = l_Lake_joinRelative(x_4, x_35);
x_42 = l_Lake_joinRelative(x_3, x_36);
x_43 = l_System_FilePath_isDir(x_42, x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_65 = lean_unbox(x_44);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_44);
x_66 = lean_ctor_get(x_2, 5);
x_67 = l_Lean_NameMap_find_x3f(lean_box(0), x_66, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_67) == 0)
{
lean_inc(x_21);
x_46 = x_21;
goto block_64;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_46 = x_68;
goto block_64;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_114; 
x_69 = lean_mk_string_unchecked("HEAD", 4, 4);
x_70 = lean_mk_string_unchecked("rev-parse", 9, 9);
x_71 = lean_mk_string_unchecked("--verify", 8, 8);
x_72 = lean_mk_string_unchecked("--end-of-options", 16, 16);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_mk_empty_array_with_capacity(x_73);
x_75 = lean_array_push(x_74, x_70);
x_76 = lean_array_push(x_75, x_71);
x_77 = lean_array_push(x_76, x_72);
x_78 = lean_array_push(x_77, x_69);
x_79 = lean_box(1);
x_80 = lean_alloc_ctor(0, 0, 3);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, 0, x_81);
x_82 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, 1, x_82);
x_83 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, 2, x_83);
x_84 = lean_mk_string_unchecked("git", 3, 3);
lean_inc(x_42);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_42);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_mk_empty_array_with_capacity(x_86);
lean_inc(x_87);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_80);
x_88 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_78);
lean_ctor_set(x_88, 3, x_85);
lean_ctor_set(x_88, 4, x_87);
x_89 = lean_unbox(x_44);
lean_ctor_set_uint8(x_88, sizeof(void*)*5, x_89);
x_90 = lean_unbox(x_32);
lean_ctor_set_uint8(x_88, sizeof(void*)*5 + 1, x_90);
x_91 = l_Lake_captureProc_x3f(x_88, x_45);
lean_dec(x_88);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_22);
lean_inc(x_95);
x_114 = l___private_Init_Data_Option_Basic_0__Option_decEqOption___redArg____x40_Init_Data_Option_Basic___hyg_4_(x_94, x_92, x_95);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_44);
x_115 = lean_ctor_get(x_2, 5);
x_116 = l_Lean_NameMap_find_x3f(lean_box(0), x_115, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_116) == 0)
{
lean_inc(x_21);
x_96 = x_21;
goto block_113;
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_96 = x_117;
goto block_113;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_95);
lean_dec(x_31);
x_118 = lean_mk_string_unchecked("diff", 4, 4);
x_119 = lean_mk_string_unchecked("--exit-code", 11, 11);
x_120 = lean_unsigned_to_nat(2u);
x_121 = lean_mk_empty_array_with_capacity(x_120);
x_122 = lean_array_push(x_121, x_118);
x_123 = lean_array_push(x_122, x_119);
x_124 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_124, 0, x_80);
lean_ctor_set(x_124, 1, x_84);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_85);
lean_ctor_set(x_124, 4, x_87);
x_125 = lean_unbox(x_44);
lean_dec(x_44);
lean_ctor_set_uint8(x_124, sizeof(void*)*5, x_125);
x_126 = lean_unbox(x_32);
lean_ctor_set_uint8(x_124, sizeof(void*)*5 + 1, x_126);
x_127 = l_Lake_testProc(x_124, x_93);
lean_dec(x_124);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_mk_string_unchecked(": repository '", 14, 14);
x_132 = lean_string_append(x_35, x_131);
lean_dec(x_131);
x_133 = lean_string_append(x_132, x_42);
lean_dec(x_42);
x_134 = lean_mk_string_unchecked("' has local changes", 19, 19);
x_135 = lean_string_append(x_133, x_134);
lean_dec(x_134);
x_136 = lean_box(2);
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_135);
x_138 = lean_unbox(x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_138);
x_139 = lean_array_push(x_5, x_137);
x_37 = x_139;
x_38 = x_130;
goto block_41;
}
else
{
lean_object* x_140; 
lean_dec(x_42);
lean_dec(x_35);
x_140 = lean_ctor_get(x_127, 1);
lean_inc(x_140);
lean_dec(x_127);
x_37 = x_5;
x_38 = x_140;
goto block_41;
}
}
block_113:
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Lake_updateGitRepo(x_35, x_42, x_96, x_95, x_5, x_93);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_37 = x_100;
x_38 = x_99;
goto block_41;
}
else
{
uint8_t x_101; 
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_97);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_97, 0);
lean_dec(x_102);
x_103 = !lean_is_exclusive(x_98);
if (x_103 == 0)
{
return x_97;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_98, 0);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_97, 0, x_106);
return x_97;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_97, 1);
lean_inc(x_107);
lean_dec(x_97);
x_108 = lean_ctor_get(x_98, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_98, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_110 = x_98;
} else {
 lean_dec_ref(x_98);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
}
}
}
block_30:
{
lean_object* x_27; 
x_27 = l_Lake_Git_filterUrl_x3f(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_mk_string_unchecked("", 0, 0);
x_7 = x_24;
x_8 = x_26;
x_9 = x_25;
x_10 = x_28;
goto block_14;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_7 = x_24;
x_8 = x_26;
x_9 = x_25;
x_10 = x_29;
goto block_14;
}
}
block_41:
{
if (lean_obj_tag(x_23) == 0)
{
x_24 = x_38;
x_25 = x_37;
x_26 = x_36;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
lean_dec(x_23);
x_40 = l_Lake_joinRelative(x_36, x_39);
lean_dec(x_39);
x_24 = x_38;
x_25 = x_37;
x_26 = x_40;
goto block_30;
}
}
block_64:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_22);
x_48 = l_Lake_cloneGitPkg(x_35, x_42, x_46, x_47, x_5, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_37 = x_51;
x_38 = x_50;
goto block_41;
}
else
{
uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_48, 0, x_57);
return x_48;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_61 = x_49;
} else {
 lean_dec_ref(x_49);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
return x_63;
}
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_materialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_PackageEntry_materialize(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Reservoir(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Materialize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Reservoir(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedMaterializedDep = _init_l_Lake_instInhabitedMaterializedDep();
lean_mark_persistent(l_Lake_instInhabitedMaterializedDep);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
