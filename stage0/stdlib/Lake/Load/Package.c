// Lean compiler output
// Module: Lake.Load.Package
// Imports: Lake.Load.Lean Lake.Load.Toml
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
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
lean_object* l_Prod_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1___boxed(lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configFileExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("lean", 4, 4);
lean_inc(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
lean_dec(x_4);
x_6 = l_System_FilePath_pathExists(x_5, x_2);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("toml", 4, 4);
x_11 = l_System_FilePath_addExtension(x_1, x_10);
lean_dec(x_10);
x_12 = l_System_FilePath_pathExists(x_11, x_9);
lean_dec(x_11);
return x_12;
}
else
{
lean_dec(x_1);
return x_6;
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_System_FilePath_pathExists(x_1, x_2);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_realConfigFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_extension(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_mk_string_unchecked("lean", 4, 4);
lean_inc(x_1);
x_5 = l_System_FilePath_addExtension(x_1, x_4);
lean_dec(x_4);
x_6 = l_Lake_resolvePath(x_5, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_7);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_instDecidableEqPos(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_12 = lean_mk_string_unchecked("toml", 4, 4);
x_13 = l_System_FilePath_addExtension(x_1, x_12);
lean_dec(x_12);
x_14 = l_Lake_resolvePath(x_13, x_8);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = l_Lake_resolvePath(x_1, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 5);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l_System_FilePath_extension(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_mk_string_unchecked("lean", 4, 4);
lean_inc(x_5);
x_8 = l_System_FilePath_addExtension(x_5, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
lean_inc(x_9);
x_10 = l_Lake_joinRelative(x_9, x_8);
lean_inc(x_10);
x_11 = l_Lake_resolvePath(x_10, x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_mk_string_unchecked("toml", 4, 4);
x_16 = l_System_FilePath_addExtension(x_5, x_15);
lean_dec(x_15);
lean_inc(x_9);
x_17 = l_Lake_joinRelative(x_9, x_16);
x_18 = lean_string_utf8_byte_size(x_13);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_instDecidableEqPos(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_82; 
lean_free_object(x_11);
lean_dec(x_10);
x_21 = l_System_FilePath_pathExists(x_17, x_14);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_82 = lean_unbox(x_22);
lean_dec(x_22);
if (x_82 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
x_24 = x_3;
goto block_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_83 = lean_mk_string_unchecked(": ", 2, 2);
x_84 = lean_string_append(x_1, x_83);
lean_dec(x_83);
x_85 = lean_string_append(x_84, x_8);
x_86 = lean_mk_string_unchecked(" and ", 5, 5);
x_87 = lean_string_append(x_85, x_86);
lean_dec(x_86);
x_88 = lean_string_append(x_87, x_16);
lean_dec(x_16);
x_89 = lean_mk_string_unchecked(" are both present; using ", 25, 25);
x_90 = lean_string_append(x_88, x_89);
lean_dec(x_89);
x_91 = lean_string_append(x_90, x_8);
x_92 = lean_box(1);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
x_94 = lean_unbox(x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_94);
x_95 = lean_array_push(x_3, x_93);
x_24 = x_95;
goto block_81;
}
block_81:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 8);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 9);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_35 = lean_ctor_get(x_2, 10);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 11);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_9);
lean_ctor_set(x_37, 5, x_8);
lean_ctor_set(x_37, 6, x_13);
lean_ctor_set(x_37, 7, x_29);
lean_ctor_set(x_37, 8, x_30);
lean_ctor_set(x_37, 9, x_31);
lean_ctor_set(x_37, 10, x_35);
lean_ctor_set(x_37, 11, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*12, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*12 + 1, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*12 + 2, x_34);
x_38 = l_Lake_loadLeanConfig(x_37, x_24, x_23);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_39, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 1);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_40, 1, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_39, 0, x_51);
return x_38;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_dec(x_39);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_55 = x_40;
} else {
 lean_dec_ref(x_40);
 x_55 = lean_box(0);
}
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
lean_ctor_set(x_38, 0, x_58);
return x_38;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_dec(x_38);
x_60 = lean_ctor_get(x_39, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_61 = x_39;
} else {
 lean_dec_ref(x_39);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_40, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_64 = x_40;
} else {
 lean_dec_ref(x_40);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_61;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_38);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_38, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_39);
if (x_71 == 0)
{
return x_38;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
x_73 = lean_ctor_get(x_39, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_39);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_38, 0, x_74);
return x_38;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
lean_dec(x_38);
x_76 = lean_ctor_get(x_39, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_78 = x_39;
} else {
 lean_dec_ref(x_39);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
}
}
else
{
lean_object* x_96; uint8_t x_97; 
lean_dec(x_13);
lean_dec(x_8);
lean_inc(x_17);
x_96 = l_Lake_resolvePath(x_17, x_14);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
x_100 = lean_string_utf8_byte_size(x_98);
x_101 = l_instDecidableEqPos(x_100, x_19);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_free_object(x_96);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_1);
x_102 = lean_ctor_get(x_2, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_2, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_2, 7);
lean_inc(x_106);
x_107 = lean_ctor_get(x_2, 8);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 9);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_110 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_111 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_112 = lean_ctor_get(x_2, 10);
lean_inc(x_112);
x_113 = lean_ctor_get(x_2, 11);
lean_inc(x_113);
lean_dec(x_2);
x_114 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_114, 0, x_102);
lean_ctor_set(x_114, 1, x_103);
lean_ctor_set(x_114, 2, x_104);
lean_ctor_set(x_114, 3, x_105);
lean_ctor_set(x_114, 4, x_9);
lean_ctor_set(x_114, 5, x_16);
lean_ctor_set(x_114, 6, x_98);
lean_ctor_set(x_114, 7, x_106);
lean_ctor_set(x_114, 8, x_107);
lean_ctor_set(x_114, 9, x_108);
lean_ctor_set(x_114, 10, x_112);
lean_ctor_set(x_114, 11, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*12, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*12 + 1, x_110);
lean_ctor_set_uint8(x_114, sizeof(void*)*12 + 2, x_111);
x_115 = l_Lake_loadTomlConfig(x_114, x_3, x_99);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_115, 0);
lean_dec(x_118);
x_119 = !lean_is_exclusive(x_116);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_116, 0);
x_121 = lean_box(0);
lean_ctor_set(x_11, 1, x_121);
lean_ctor_set(x_11, 0, x_120);
lean_ctor_set(x_116, 0, x_11);
return x_115;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_116, 0);
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_116);
x_124 = lean_box(0);
lean_ctor_set(x_11, 1, x_124);
lean_ctor_set(x_11, 0, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_11);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_115, 0, x_125);
return x_115;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_dec(x_115);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_116, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_129 = x_116;
} else {
 lean_dec_ref(x_116);
 x_129 = lean_box(0);
}
x_130 = lean_box(0);
lean_ctor_set(x_11, 1, x_130);
lean_ctor_set(x_11, 0, x_127);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_11);
lean_ctor_set(x_131, 1, x_128);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_126);
return x_132;
}
}
else
{
uint8_t x_133; 
lean_free_object(x_11);
x_133 = !lean_is_exclusive(x_115);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_115, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_116);
if (x_135 == 0)
{
return x_115;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_116, 0);
x_137 = lean_ctor_get(x_116, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_116);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_115, 0, x_138);
return x_115;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_115, 1);
lean_inc(x_139);
lean_dec(x_115);
x_140 = lean_ctor_get(x_116, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_116, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_142 = x_116;
} else {
 lean_dec_ref(x_116);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_98);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_2);
x_145 = lean_mk_string_unchecked(": no configuration file with a supported extension:\n", 52, 52);
x_146 = lean_string_append(x_1, x_145);
lean_dec(x_145);
x_147 = lean_string_append(x_146, x_10);
lean_dec(x_10);
x_148 = lean_mk_string_unchecked("\n", 1, 1);
x_149 = lean_string_append(x_147, x_148);
lean_dec(x_148);
x_150 = lean_string_append(x_149, x_17);
lean_dec(x_17);
x_151 = lean_box(3);
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_150);
x_153 = lean_unbox(x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_153);
x_154 = lean_array_get_size(x_3);
x_155 = lean_array_push(x_3, x_152);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_155);
lean_ctor_set(x_11, 0, x_154);
lean_ctor_set(x_96, 0, x_11);
return x_96;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_96, 0);
x_157 = lean_ctor_get(x_96, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_96);
x_158 = lean_string_utf8_byte_size(x_156);
x_159 = l_instDecidableEqPos(x_158, x_19);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_1);
x_160 = lean_ctor_get(x_2, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_2, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_2, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_2, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_2, 7);
lean_inc(x_164);
x_165 = lean_ctor_get(x_2, 8);
lean_inc(x_165);
x_166 = lean_ctor_get(x_2, 9);
lean_inc(x_166);
x_167 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_168 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_169 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_170 = lean_ctor_get(x_2, 10);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 11);
lean_inc(x_171);
lean_dec(x_2);
x_172 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_172, 0, x_160);
lean_ctor_set(x_172, 1, x_161);
lean_ctor_set(x_172, 2, x_162);
lean_ctor_set(x_172, 3, x_163);
lean_ctor_set(x_172, 4, x_9);
lean_ctor_set(x_172, 5, x_16);
lean_ctor_set(x_172, 6, x_156);
lean_ctor_set(x_172, 7, x_164);
lean_ctor_set(x_172, 8, x_165);
lean_ctor_set(x_172, 9, x_166);
lean_ctor_set(x_172, 10, x_170);
lean_ctor_set(x_172, 11, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*12, x_167);
lean_ctor_set_uint8(x_172, sizeof(void*)*12 + 1, x_168);
lean_ctor_set_uint8(x_172, sizeof(void*)*12 + 2, x_169);
x_173 = l_Lake_loadTomlConfig(x_172, x_3, x_157);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_174, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_179 = x_174;
} else {
 lean_dec_ref(x_174);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
lean_ctor_set(x_11, 1, x_180);
lean_ctor_set(x_11, 0, x_177);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_11);
lean_ctor_set(x_181, 1, x_178);
if (lean_is_scalar(x_176)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_176;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_175);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_free_object(x_11);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_184 = x_173;
} else {
 lean_dec_ref(x_173);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_174, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_187 = x_174;
} else {
 lean_dec_ref(x_174);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
if (lean_is_scalar(x_184)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_184;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_183);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_156);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_2);
x_190 = lean_mk_string_unchecked(": no configuration file with a supported extension:\n", 52, 52);
x_191 = lean_string_append(x_1, x_190);
lean_dec(x_190);
x_192 = lean_string_append(x_191, x_10);
lean_dec(x_10);
x_193 = lean_mk_string_unchecked("\n", 1, 1);
x_194 = lean_string_append(x_192, x_193);
lean_dec(x_193);
x_195 = lean_string_append(x_194, x_17);
lean_dec(x_17);
x_196 = lean_box(3);
x_197 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_197, 0, x_195);
x_198 = lean_unbox(x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_198);
x_199 = lean_array_get_size(x_3);
x_200 = lean_array_push(x_3, x_197);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_200);
lean_ctor_set(x_11, 0, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_11);
lean_ctor_set(x_201, 1, x_157);
return x_201;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_202 = lean_ctor_get(x_11, 0);
x_203 = lean_ctor_get(x_11, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_11);
x_204 = lean_mk_string_unchecked("toml", 4, 4);
x_205 = l_System_FilePath_addExtension(x_5, x_204);
lean_dec(x_204);
lean_inc(x_9);
x_206 = l_Lake_joinRelative(x_9, x_205);
x_207 = lean_string_utf8_byte_size(x_202);
x_208 = lean_unsigned_to_nat(0u);
x_209 = l_instDecidableEqPos(x_207, x_208);
lean_dec(x_207);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_249; 
lean_dec(x_10);
x_210 = l_System_FilePath_pathExists(x_206, x_203);
lean_dec(x_206);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_249 = lean_unbox(x_211);
lean_dec(x_211);
if (x_249 == 0)
{
lean_dec(x_205);
lean_dec(x_1);
x_213 = x_3;
goto block_248;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; 
x_250 = lean_mk_string_unchecked(": ", 2, 2);
x_251 = lean_string_append(x_1, x_250);
lean_dec(x_250);
x_252 = lean_string_append(x_251, x_8);
x_253 = lean_mk_string_unchecked(" and ", 5, 5);
x_254 = lean_string_append(x_252, x_253);
lean_dec(x_253);
x_255 = lean_string_append(x_254, x_205);
lean_dec(x_205);
x_256 = lean_mk_string_unchecked(" are both present; using ", 25, 25);
x_257 = lean_string_append(x_255, x_256);
lean_dec(x_256);
x_258 = lean_string_append(x_257, x_8);
x_259 = lean_box(1);
x_260 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_260, 0, x_258);
x_261 = lean_unbox(x_259);
lean_ctor_set_uint8(x_260, sizeof(void*)*1, x_261);
x_262 = lean_array_push(x_3, x_260);
x_213 = x_262;
goto block_248;
}
block_248:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_214 = lean_ctor_get(x_2, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_2, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_2, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_2, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_2, 7);
lean_inc(x_218);
x_219 = lean_ctor_get(x_2, 8);
lean_inc(x_219);
x_220 = lean_ctor_get(x_2, 9);
lean_inc(x_220);
x_221 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_222 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_223 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_224 = lean_ctor_get(x_2, 10);
lean_inc(x_224);
x_225 = lean_ctor_get(x_2, 11);
lean_inc(x_225);
lean_dec(x_2);
x_226 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_226, 0, x_214);
lean_ctor_set(x_226, 1, x_215);
lean_ctor_set(x_226, 2, x_216);
lean_ctor_set(x_226, 3, x_217);
lean_ctor_set(x_226, 4, x_9);
lean_ctor_set(x_226, 5, x_8);
lean_ctor_set(x_226, 6, x_202);
lean_ctor_set(x_226, 7, x_218);
lean_ctor_set(x_226, 8, x_219);
lean_ctor_set(x_226, 9, x_220);
lean_ctor_set(x_226, 10, x_224);
lean_ctor_set(x_226, 11, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*12, x_221);
lean_ctor_set_uint8(x_226, sizeof(void*)*12 + 1, x_222);
lean_ctor_set_uint8(x_226, sizeof(void*)*12 + 2, x_223);
x_227 = l_Lake_loadLeanConfig(x_226, x_213, x_212);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_231 = x_227;
} else {
 lean_dec_ref(x_227);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_228, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_233 = x_228;
} else {
 lean_dec_ref(x_228);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_229, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_236 = x_229;
} else {
 lean_dec_ref(x_229);
 x_236 = lean_box(0);
}
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_235);
if (lean_is_scalar(x_236)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_236;
}
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_237);
if (lean_is_scalar(x_233)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_233;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_232);
if (lean_is_scalar(x_231)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_231;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_230);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_241 = lean_ctor_get(x_227, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_242 = x_227;
} else {
 lean_dec_ref(x_227);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_228, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_228, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_245 = x_228;
} else {
 lean_dec_ref(x_228);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_241);
return x_247;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
lean_dec(x_202);
lean_dec(x_8);
lean_inc(x_206);
x_263 = l_Lake_resolvePath(x_206, x_203);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_267 = lean_string_utf8_byte_size(x_264);
x_268 = l_instDecidableEqPos(x_267, x_208);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_266);
lean_dec(x_206);
lean_dec(x_10);
lean_dec(x_1);
x_269 = lean_ctor_get(x_2, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_2, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_2, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_2, 3);
lean_inc(x_272);
x_273 = lean_ctor_get(x_2, 7);
lean_inc(x_273);
x_274 = lean_ctor_get(x_2, 8);
lean_inc(x_274);
x_275 = lean_ctor_get(x_2, 9);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_277 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_278 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_279 = lean_ctor_get(x_2, 10);
lean_inc(x_279);
x_280 = lean_ctor_get(x_2, 11);
lean_inc(x_280);
lean_dec(x_2);
x_281 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_281, 0, x_269);
lean_ctor_set(x_281, 1, x_270);
lean_ctor_set(x_281, 2, x_271);
lean_ctor_set(x_281, 3, x_272);
lean_ctor_set(x_281, 4, x_9);
lean_ctor_set(x_281, 5, x_205);
lean_ctor_set(x_281, 6, x_264);
lean_ctor_set(x_281, 7, x_273);
lean_ctor_set(x_281, 8, x_274);
lean_ctor_set(x_281, 9, x_275);
lean_ctor_set(x_281, 10, x_279);
lean_ctor_set(x_281, 11, x_280);
lean_ctor_set_uint8(x_281, sizeof(void*)*12, x_276);
lean_ctor_set_uint8(x_281, sizeof(void*)*12 + 1, x_277);
lean_ctor_set_uint8(x_281, sizeof(void*)*12 + 2, x_278);
x_282 = l_Lake_loadTomlConfig(x_281, x_3, x_265);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_285 = x_282;
} else {
 lean_dec_ref(x_282);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_283, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_288 = x_283;
} else {
 lean_dec_ref(x_283);
 x_288 = lean_box(0);
}
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_286);
lean_ctor_set(x_290, 1, x_289);
if (lean_is_scalar(x_288)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_288;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_287);
if (lean_is_scalar(x_285)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_285;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_284);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_293 = lean_ctor_get(x_282, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_294 = x_282;
} else {
 lean_dec_ref(x_282);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_283, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_283, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_297 = x_283;
} else {
 lean_dec_ref(x_283);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
if (lean_is_scalar(x_294)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_294;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_293);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_264);
lean_dec(x_205);
lean_dec(x_9);
lean_dec(x_2);
x_300 = lean_mk_string_unchecked(": no configuration file with a supported extension:\n", 52, 52);
x_301 = lean_string_append(x_1, x_300);
lean_dec(x_300);
x_302 = lean_string_append(x_301, x_10);
lean_dec(x_10);
x_303 = lean_mk_string_unchecked("\n", 1, 1);
x_304 = lean_string_append(x_302, x_303);
lean_dec(x_303);
x_305 = lean_string_append(x_304, x_206);
lean_dec(x_206);
x_306 = lean_box(3);
x_307 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_307, 0, x_305);
x_308 = lean_unbox(x_306);
lean_ctor_set_uint8(x_307, sizeof(void*)*1, x_308);
x_309 = lean_array_get_size(x_3);
x_310 = lean_array_push(x_3, x_307);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
if (lean_is_scalar(x_266)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_266;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_265);
return x_312;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_313 = lean_ctor_get(x_6, 0);
lean_inc(x_313);
lean_dec(x_6);
x_314 = lean_ctor_get(x_2, 6);
lean_inc(x_314);
lean_inc(x_314);
x_315 = l_Lake_resolvePath(x_314, x_4);
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_317 = lean_ctor_get(x_315, 0);
x_318 = lean_ctor_get(x_315, 1);
x_319 = lean_string_utf8_byte_size(x_317);
x_320 = lean_unsigned_to_nat(0u);
x_321 = l_instDecidableEqPos(x_319, x_320);
lean_dec(x_319);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec(x_314);
x_322 = lean_ctor_get(x_2, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_2, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_2, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_2, 3);
lean_inc(x_325);
x_326 = lean_ctor_get(x_2, 4);
lean_inc(x_326);
x_327 = lean_ctor_get(x_2, 7);
lean_inc(x_327);
x_328 = lean_ctor_get(x_2, 8);
lean_inc(x_328);
x_329 = lean_ctor_get(x_2, 9);
lean_inc(x_329);
x_330 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_331 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_332 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_333 = lean_ctor_get(x_2, 10);
lean_inc(x_333);
x_334 = lean_ctor_get(x_2, 11);
lean_inc(x_334);
lean_dec(x_2);
lean_inc(x_317);
x_335 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_335, 0, x_322);
lean_ctor_set(x_335, 1, x_323);
lean_ctor_set(x_335, 2, x_324);
lean_ctor_set(x_335, 3, x_325);
lean_ctor_set(x_335, 4, x_326);
lean_ctor_set(x_335, 5, x_5);
lean_ctor_set(x_335, 6, x_317);
lean_ctor_set(x_335, 7, x_327);
lean_ctor_set(x_335, 8, x_328);
lean_ctor_set(x_335, 9, x_329);
lean_ctor_set(x_335, 10, x_333);
lean_ctor_set(x_335, 11, x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*12, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*12 + 1, x_331);
lean_ctor_set_uint8(x_335, sizeof(void*)*12 + 2, x_332);
x_336 = lean_mk_string_unchecked("lean", 4, 4);
x_337 = lean_string_dec_eq(x_313, x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; uint8_t x_339; 
x_338 = lean_mk_string_unchecked("toml", 4, 4);
x_339 = lean_string_dec_eq(x_313, x_338);
lean_dec(x_338);
lean_dec(x_313);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_335);
x_340 = lean_mk_string_unchecked(": configuration has unsupported file extension: ", 48, 48);
x_341 = lean_string_append(x_1, x_340);
lean_dec(x_340);
x_342 = lean_string_append(x_341, x_317);
lean_dec(x_317);
x_343 = lean_box(3);
x_344 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_344, 0, x_342);
x_345 = lean_unbox(x_343);
lean_ctor_set_uint8(x_344, sizeof(void*)*1, x_345);
x_346 = lean_array_get_size(x_3);
x_347 = lean_array_push(x_3, x_344);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
lean_ctor_set(x_315, 0, x_348);
return x_315;
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_free_object(x_315);
lean_dec(x_317);
lean_dec(x_1);
x_349 = l_Lake_loadTomlConfig(x_335, x_3, x_318);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
uint8_t x_351; 
x_351 = !lean_is_exclusive(x_349);
if (x_351 == 0)
{
lean_object* x_352; uint8_t x_353; 
x_352 = lean_ctor_get(x_349, 0);
lean_dec(x_352);
x_353 = !lean_is_exclusive(x_350);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_350, 0);
x_355 = lean_box(0);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set(x_350, 0, x_356);
return x_349;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_357 = lean_ctor_get(x_350, 0);
x_358 = lean_ctor_get(x_350, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_350);
x_359 = lean_box(0);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_359);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_358);
lean_ctor_set(x_349, 0, x_361);
return x_349;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_362 = lean_ctor_get(x_349, 1);
lean_inc(x_362);
lean_dec(x_349);
x_363 = lean_ctor_get(x_350, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = lean_box(0);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_363);
lean_ctor_set(x_367, 1, x_366);
if (lean_is_scalar(x_365)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_365;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_364);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_362);
return x_369;
}
}
else
{
uint8_t x_370; 
x_370 = !lean_is_exclusive(x_349);
if (x_370 == 0)
{
lean_object* x_371; uint8_t x_372; 
x_371 = lean_ctor_get(x_349, 0);
lean_dec(x_371);
x_372 = !lean_is_exclusive(x_350);
if (x_372 == 0)
{
return x_349;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_350, 0);
x_374 = lean_ctor_get(x_350, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_350);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set(x_349, 0, x_375);
return x_349;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_349, 1);
lean_inc(x_376);
lean_dec(x_349);
x_377 = lean_ctor_get(x_350, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_350, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_379 = x_350;
} else {
 lean_dec_ref(x_350);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_376);
return x_381;
}
}
}
}
else
{
lean_object* x_382; lean_object* x_383; 
lean_free_object(x_315);
lean_dec(x_317);
lean_dec(x_313);
lean_dec(x_1);
x_382 = l_Lake_loadLeanConfig(x_335, x_3, x_318);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
if (lean_obj_tag(x_383) == 0)
{
uint8_t x_384; 
x_384 = !lean_is_exclusive(x_382);
if (x_384 == 0)
{
lean_object* x_385; uint8_t x_386; 
x_385 = lean_ctor_get(x_382, 0);
lean_dec(x_385);
x_386 = !lean_is_exclusive(x_383);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_387 = lean_ctor_get(x_383, 0);
x_388 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_389 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_390 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_389, x_388, x_387);
lean_ctor_set(x_383, 0, x_390);
return x_382;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_391 = lean_ctor_get(x_383, 0);
x_392 = lean_ctor_get(x_383, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_383);
x_393 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_394 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_395 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_394, x_393, x_391);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_392);
lean_ctor_set(x_382, 0, x_396);
return x_382;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_397 = lean_ctor_get(x_382, 1);
lean_inc(x_397);
lean_dec(x_382);
x_398 = lean_ctor_get(x_383, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_383, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_400 = x_383;
} else {
 lean_dec_ref(x_383);
 x_400 = lean_box(0);
}
x_401 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_402 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_403 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_402, x_401, x_398);
if (lean_is_scalar(x_400)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_400;
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_399);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_397);
return x_405;
}
}
else
{
uint8_t x_406; 
x_406 = !lean_is_exclusive(x_382);
if (x_406 == 0)
{
lean_object* x_407; uint8_t x_408; 
x_407 = lean_ctor_get(x_382, 0);
lean_dec(x_407);
x_408 = !lean_is_exclusive(x_383);
if (x_408 == 0)
{
return x_382;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_383, 0);
x_410 = lean_ctor_get(x_383, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_383);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_382, 0, x_411);
return x_382;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_412 = lean_ctor_get(x_382, 1);
lean_inc(x_412);
lean_dec(x_382);
x_413 = lean_ctor_get(x_383, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_383, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_415 = x_383;
} else {
 lean_dec_ref(x_383);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_414);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_412);
return x_417;
}
}
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_317);
lean_dec(x_313);
lean_dec(x_5);
lean_dec(x_2);
x_418 = lean_mk_string_unchecked(": configuration file not found: ", 32, 32);
x_419 = lean_string_append(x_1, x_418);
lean_dec(x_418);
x_420 = lean_string_append(x_419, x_314);
lean_dec(x_314);
x_421 = lean_box(3);
x_422 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_422, 0, x_420);
x_423 = lean_unbox(x_421);
lean_ctor_set_uint8(x_422, sizeof(void*)*1, x_423);
x_424 = lean_array_get_size(x_3);
x_425 = lean_array_push(x_3, x_422);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
lean_ctor_set(x_315, 0, x_426);
return x_315;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
x_427 = lean_ctor_get(x_315, 0);
x_428 = lean_ctor_get(x_315, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_315);
x_429 = lean_string_utf8_byte_size(x_427);
x_430 = lean_unsigned_to_nat(0u);
x_431 = l_instDecidableEqPos(x_429, x_430);
lean_dec(x_429);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; uint8_t x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
lean_dec(x_314);
x_432 = lean_ctor_get(x_2, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_2, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_2, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_2, 3);
lean_inc(x_435);
x_436 = lean_ctor_get(x_2, 4);
lean_inc(x_436);
x_437 = lean_ctor_get(x_2, 7);
lean_inc(x_437);
x_438 = lean_ctor_get(x_2, 8);
lean_inc(x_438);
x_439 = lean_ctor_get(x_2, 9);
lean_inc(x_439);
x_440 = lean_ctor_get_uint8(x_2, sizeof(void*)*12);
x_441 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 1);
x_442 = lean_ctor_get_uint8(x_2, sizeof(void*)*12 + 2);
x_443 = lean_ctor_get(x_2, 10);
lean_inc(x_443);
x_444 = lean_ctor_get(x_2, 11);
lean_inc(x_444);
lean_dec(x_2);
lean_inc(x_427);
x_445 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_445, 0, x_432);
lean_ctor_set(x_445, 1, x_433);
lean_ctor_set(x_445, 2, x_434);
lean_ctor_set(x_445, 3, x_435);
lean_ctor_set(x_445, 4, x_436);
lean_ctor_set(x_445, 5, x_5);
lean_ctor_set(x_445, 6, x_427);
lean_ctor_set(x_445, 7, x_437);
lean_ctor_set(x_445, 8, x_438);
lean_ctor_set(x_445, 9, x_439);
lean_ctor_set(x_445, 10, x_443);
lean_ctor_set(x_445, 11, x_444);
lean_ctor_set_uint8(x_445, sizeof(void*)*12, x_440);
lean_ctor_set_uint8(x_445, sizeof(void*)*12 + 1, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*12 + 2, x_442);
x_446 = lean_mk_string_unchecked("lean", 4, 4);
x_447 = lean_string_dec_eq(x_313, x_446);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; uint8_t x_449; 
x_448 = lean_mk_string_unchecked("toml", 4, 4);
x_449 = lean_string_dec_eq(x_313, x_448);
lean_dec(x_448);
lean_dec(x_313);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_445);
x_450 = lean_mk_string_unchecked(": configuration has unsupported file extension: ", 48, 48);
x_451 = lean_string_append(x_1, x_450);
lean_dec(x_450);
x_452 = lean_string_append(x_451, x_427);
lean_dec(x_427);
x_453 = lean_box(3);
x_454 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_454, 0, x_452);
x_455 = lean_unbox(x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*1, x_455);
x_456 = lean_array_get_size(x_3);
x_457 = lean_array_push(x_3, x_454);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_428);
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_427);
lean_dec(x_1);
x_460 = l_Lake_loadTomlConfig(x_445, x_3, x_428);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_463 = x_460;
} else {
 lean_dec_ref(x_460);
 x_463 = lean_box(0);
}
x_464 = lean_ctor_get(x_461, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_461, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_466 = x_461;
} else {
 lean_dec_ref(x_461);
 x_466 = lean_box(0);
}
x_467 = lean_box(0);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_464);
lean_ctor_set(x_468, 1, x_467);
if (lean_is_scalar(x_466)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_466;
}
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_465);
if (lean_is_scalar(x_463)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_463;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_462);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_471 = lean_ctor_get(x_460, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_472 = x_460;
} else {
 lean_dec_ref(x_460);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_475 = x_461;
} else {
 lean_dec_ref(x_461);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
if (lean_is_scalar(x_472)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_472;
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_471);
return x_477;
}
}
}
else
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_427);
lean_dec(x_313);
lean_dec(x_1);
x_478 = l_Lake_loadLeanConfig(x_445, x_3, x_428);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_481 = x_478;
} else {
 lean_dec_ref(x_478);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_479, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_479, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_484 = x_479;
} else {
 lean_dec_ref(x_479);
 x_484 = lean_box(0);
}
x_485 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__0), 1, 0);
x_486 = lean_alloc_closure((void*)(l_Lake_loadPackageCore___lam__1___boxed), 1, 0);
x_487 = l_Prod_map(lean_box(0), lean_box(0), lean_box(0), lean_box(0), x_486, x_485, x_482);
if (lean_is_scalar(x_484)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_484;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_483);
if (lean_is_scalar(x_481)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_481;
}
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_480);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_490 = lean_ctor_get(x_478, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_491 = x_478;
} else {
 lean_dec_ref(x_478);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_479, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_479, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_494 = x_479;
} else {
 lean_dec_ref(x_479);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_492);
lean_ctor_set(x_495, 1, x_493);
if (lean_is_scalar(x_491)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_491;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_490);
return x_496;
}
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_427);
lean_dec(x_313);
lean_dec(x_5);
lean_dec(x_2);
x_497 = lean_mk_string_unchecked(": configuration file not found: ", 32, 32);
x_498 = lean_string_append(x_1, x_497);
lean_dec(x_497);
x_499 = lean_string_append(x_498, x_314);
lean_dec(x_314);
x_500 = lean_box(3);
x_501 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_501, 0, x_499);
x_502 = lean_unbox(x_500);
lean_ctor_set_uint8(x_501, sizeof(void*)*1, x_502);
x_503 = lean_array_get_size(x_3);
x_504 = lean_array_push(x_3, x_501);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_428);
return x_506;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackageCore___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_loadPackageCore___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_loadPackage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_searchPathRef;
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lake_Env_leanSearchPath(x_5);
lean_dec(x_5);
x_7 = lean_st_ref_set(x_4, x_6, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("[root]", 6, 6);
x_10 = l_Lake_loadPackageCore(x_9, x_1, x_2, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_24 = x_11;
} else {
 lean_dec_ref(x_11);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_10, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_10, 0, x_33);
return x_10;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_dec(x_10);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_37 = x_11;
} else {
 lean_dec_ref(x_11);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
}
lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Toml(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Toml(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
