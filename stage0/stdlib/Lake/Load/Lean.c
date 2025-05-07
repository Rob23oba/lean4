// Lean compiler output
// Module: Lake.Load.Lean
// Imports: Lake.Load.Lean.Elab Lake.Load.Lean.Eval
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
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_PackageDecl_loadFromEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_loadLeanConfig___lam__0(uint8_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_Package_loadFromEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
extern lean_object* l_Lake_defaultManifestFile;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_7, x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_5, x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___redArg(x_2, x_12, x_4, x_9);
return x_13;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Lake_loadLeanConfig___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lake_importConfigFile(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_1, 9);
lean_inc(x_10);
lean_inc(x_8);
x_11 = l_Lake_PackageDecl_loadFromEnv(x_8, x_10);
x_12 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_89; lean_object* x_103; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 5);
lean_inc(x_21);
x_103 = lean_ctor_get(x_16, 2);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = l_Lake_defaultManifestFile;
x_89 = x_104;
goto block_102;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_89 = x_105;
goto block_102;
}
block_66:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_16, 13);
lean_inc(x_33);
x_34 = lean_ctor_get(x_16, 15);
lean_inc(x_34);
x_35 = lean_alloc_ctor(0, 19, 0);
lean_ctor_set(x_35, 0, x_15);
lean_ctor_set(x_35, 1, x_18);
lean_ctor_set(x_35, 2, x_19);
lean_ctor_set(x_35, 3, x_16);
lean_ctor_set(x_35, 4, x_20);
lean_ctor_set(x_35, 5, x_21);
lean_ctor_set(x_35, 6, x_30);
lean_ctor_set(x_35, 7, x_27);
lean_ctor_set(x_35, 8, x_28);
lean_ctor_set(x_35, 9, x_26);
lean_ctor_set(x_35, 10, x_29);
lean_ctor_set(x_35, 11, x_25);
lean_ctor_set(x_35, 12, x_31);
lean_ctor_set(x_35, 13, x_24);
lean_ctor_set(x_35, 14, x_23);
lean_ctor_set(x_35, 15, x_22);
lean_ctor_set(x_35, 16, x_32);
lean_ctor_set(x_35, 17, x_33);
lean_ctor_set(x_35, 18, x_34);
lean_inc(x_8);
x_36 = l_Lake_Package_loadFromEnv(x_35, x_8, x_10, x_9, x_14);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 0);
if (lean_is_scalar(x_17)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_17;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_37, 0, x_42);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
if (lean_is_scalar(x_17)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_17;
}
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_8);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_36, 0, x_46);
return x_36;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_50 = x_37;
} else {
 lean_dec_ref(x_37);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_17;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_8);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_17);
lean_dec(x_8);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_36, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_37);
if (x_56 == 0)
{
return x_36;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_37, 0);
x_58 = lean_ctor_get(x_37, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_37);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_36, 0, x_59);
return x_36;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_dec(x_36);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_63 = x_37;
} else {
 lean_dec_ref(x_37);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
}
block_88:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_mk_empty_array_with_capacity(x_67);
x_75 = lean_box(0);
x_76 = lean_ctor_get(x_16, 12);
lean_inc(x_76);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_box(0);
x_78 = lean_alloc_closure((void*)(l_Lake_loadLeanConfig___lam__0___boxed), 2, 1);
lean_closure_set(x_78, 0, x_77);
x_79 = lean_unbox(x_77);
lean_inc(x_15);
x_80 = l_Lean_Name_toString(x_15, x_79, x_78);
x_81 = lean_mk_string_unchecked("-", 1, 1);
x_82 = lean_string_append(x_80, x_81);
lean_dec(x_81);
x_83 = l_System_Platform_target;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_mk_string_unchecked(".tar.gz", 7, 7);
x_86 = lean_string_append(x_84, x_85);
lean_dec(x_85);
lean_inc_n(x_74, 2);
x_22 = x_74;
x_23 = x_74;
x_24 = x_75;
x_25 = x_73;
x_26 = x_68;
x_27 = x_69;
x_28 = x_70;
x_29 = x_72;
x_30 = x_71;
x_31 = x_74;
x_32 = x_86;
goto block_66;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
lean_dec(x_76);
lean_inc_n(x_74, 2);
x_22 = x_74;
x_23 = x_74;
x_24 = x_75;
x_25 = x_73;
x_26 = x_68;
x_27 = x_69;
x_28 = x_70;
x_29 = x_72;
x_30 = x_71;
x_31 = x_74;
x_32 = x_87;
goto block_66;
}
}
block_102:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_90 = l_System_FilePath_normalize(x_89);
x_91 = lean_ctor_get(x_1, 10);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 11);
lean_inc(x_92);
lean_dec(x_1);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_mk_empty_array_with_capacity(x_93);
x_95 = lean_box(0);
x_96 = lean_array_get_size(x_94);
x_97 = lean_nat_dec_lt(x_93, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
lean_inc(x_94);
x_67 = x_93;
x_68 = x_94;
x_69 = x_91;
x_70 = x_92;
x_71 = x_90;
x_72 = x_94;
x_73 = x_95;
goto block_88;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
lean_inc(x_94);
x_67 = x_93;
x_68 = x_94;
x_69 = x_91;
x_70 = x_92;
x_71 = x_90;
x_72 = x_94;
x_73 = x_95;
goto block_88;
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; 
x_99 = lean_usize_of_nat(x_93);
x_100 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_101 = l_Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0(x_15, x_94, x_99, x_100, x_95);
lean_inc(x_94);
x_67 = x_93;
x_68 = x_94;
x_69 = x_91;
x_70 = x_92;
x_71 = x_90;
x_72 = x_94;
x_73 = x_101;
goto block_88;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_12);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_12, 0);
x_108 = lean_io_error_to_string(x_107);
x_109 = lean_box(3);
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
x_111 = lean_unbox(x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_111);
x_112 = lean_array_get_size(x_9);
x_113 = lean_array_push(x_9, x_110);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_113);
lean_ctor_set(x_5, 0, x_112);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_12, 0);
x_115 = lean_ctor_get(x_12, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_12);
x_116 = lean_io_error_to_string(x_114);
x_117 = lean_box(3);
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
x_119 = lean_unbox(x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_119);
x_120 = lean_array_get_size(x_9);
x_121 = lean_array_push(x_9, x_118);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_121);
lean_ctor_set(x_5, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_5);
lean_ctor_set(x_122, 1, x_115);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_5, 0);
x_124 = lean_ctor_get(x_5, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_5);
x_125 = lean_ctor_get(x_1, 9);
lean_inc(x_125);
lean_inc(x_123);
x_126 = l_Lake_PackageDecl_loadFromEnv(x_123, x_125);
x_127 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_126, x_6);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_191; lean_object* x_205; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_132 = x_128;
} else {
 lean_dec_ref(x_128);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_1, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_1, 6);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 5);
lean_inc(x_136);
x_205 = lean_ctor_get(x_131, 2);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = l_Lake_defaultManifestFile;
x_191 = x_206;
goto block_204;
}
else
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
lean_dec(x_205);
x_191 = x_207;
goto block_204;
}
block_168:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_131, 13);
lean_inc(x_148);
x_149 = lean_ctor_get(x_131, 15);
lean_inc(x_149);
x_150 = lean_alloc_ctor(0, 19, 0);
lean_ctor_set(x_150, 0, x_130);
lean_ctor_set(x_150, 1, x_133);
lean_ctor_set(x_150, 2, x_134);
lean_ctor_set(x_150, 3, x_131);
lean_ctor_set(x_150, 4, x_135);
lean_ctor_set(x_150, 5, x_136);
lean_ctor_set(x_150, 6, x_145);
lean_ctor_set(x_150, 7, x_142);
lean_ctor_set(x_150, 8, x_143);
lean_ctor_set(x_150, 9, x_141);
lean_ctor_set(x_150, 10, x_144);
lean_ctor_set(x_150, 11, x_140);
lean_ctor_set(x_150, 12, x_146);
lean_ctor_set(x_150, 13, x_139);
lean_ctor_set(x_150, 14, x_138);
lean_ctor_set(x_150, 15, x_137);
lean_ctor_set(x_150, 16, x_147);
lean_ctor_set(x_150, 17, x_148);
lean_ctor_set(x_150, 18, x_149);
lean_inc(x_123);
x_151 = l_Lake_Package_loadFromEnv(x_150, x_123, x_125, x_124, x_129);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_157 = x_152;
} else {
 lean_dec_ref(x_152);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_132;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_123);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_154;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_153);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_132);
lean_dec(x_123);
x_161 = lean_ctor_get(x_151, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_162 = x_151;
} else {
 lean_dec_ref(x_151);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_152, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_152, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_165 = x_152;
} else {
 lean_dec_ref(x_152);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
if (lean_is_scalar(x_162)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_162;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
return x_167;
}
}
block_190:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_mk_empty_array_with_capacity(x_169);
x_177 = lean_box(0);
x_178 = lean_ctor_get(x_131, 12);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_179 = lean_box(0);
x_180 = lean_alloc_closure((void*)(l_Lake_loadLeanConfig___lam__0___boxed), 2, 1);
lean_closure_set(x_180, 0, x_179);
x_181 = lean_unbox(x_179);
lean_inc(x_130);
x_182 = l_Lean_Name_toString(x_130, x_181, x_180);
x_183 = lean_mk_string_unchecked("-", 1, 1);
x_184 = lean_string_append(x_182, x_183);
lean_dec(x_183);
x_185 = l_System_Platform_target;
x_186 = lean_string_append(x_184, x_185);
x_187 = lean_mk_string_unchecked(".tar.gz", 7, 7);
x_188 = lean_string_append(x_186, x_187);
lean_dec(x_187);
lean_inc_n(x_176, 2);
x_137 = x_176;
x_138 = x_176;
x_139 = x_177;
x_140 = x_175;
x_141 = x_170;
x_142 = x_171;
x_143 = x_172;
x_144 = x_174;
x_145 = x_173;
x_146 = x_176;
x_147 = x_188;
goto block_168;
}
else
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_178, 0);
lean_inc(x_189);
lean_dec(x_178);
lean_inc_n(x_176, 2);
x_137 = x_176;
x_138 = x_176;
x_139 = x_177;
x_140 = x_175;
x_141 = x_170;
x_142 = x_171;
x_143 = x_172;
x_144 = x_174;
x_145 = x_173;
x_146 = x_176;
x_147 = x_189;
goto block_168;
}
}
block_204:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_192 = l_System_FilePath_normalize(x_191);
x_193 = lean_ctor_get(x_1, 10);
lean_inc(x_193);
x_194 = lean_ctor_get(x_1, 11);
lean_inc(x_194);
lean_dec(x_1);
x_195 = lean_unsigned_to_nat(0u);
x_196 = lean_mk_empty_array_with_capacity(x_195);
x_197 = lean_box(0);
x_198 = lean_array_get_size(x_196);
x_199 = lean_nat_dec_lt(x_195, x_198);
if (x_199 == 0)
{
lean_dec(x_198);
lean_inc(x_196);
x_169 = x_195;
x_170 = x_196;
x_171 = x_193;
x_172 = x_194;
x_173 = x_192;
x_174 = x_196;
x_175 = x_197;
goto block_190;
}
else
{
uint8_t x_200; 
x_200 = lean_nat_dec_le(x_198, x_198);
if (x_200 == 0)
{
lean_dec(x_198);
lean_inc(x_196);
x_169 = x_195;
x_170 = x_196;
x_171 = x_193;
x_172 = x_194;
x_173 = x_192;
x_174 = x_196;
x_175 = x_197;
goto block_190;
}
else
{
size_t x_201; size_t x_202; lean_object* x_203; 
x_201 = lean_usize_of_nat(x_195);
x_202 = lean_usize_of_nat(x_198);
lean_dec(x_198);
x_203 = l_Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0(x_130, x_196, x_201, x_202, x_197);
lean_inc(x_196);
x_169 = x_195;
x_170 = x_196;
x_171 = x_193;
x_172 = x_194;
x_173 = x_192;
x_174 = x_196;
x_175 = x_203;
goto block_190;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_1);
x_208 = lean_ctor_get(x_127, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_127, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_210 = x_127;
} else {
 lean_dec_ref(x_127);
 x_210 = lean_box(0);
}
x_211 = lean_io_error_to_string(x_208);
x_212 = lean_box(3);
x_213 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_213, 0, x_211);
x_214 = lean_unbox(x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*1, x_214);
x_215 = lean_array_get_size(x_124);
x_216 = lean_array_push(x_124, x_213);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
if (lean_is_scalar(x_210)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_210;
 lean_ctor_set_tag(x_218, 0);
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_209);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_4);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_4, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_5);
if (x_221 == 0)
{
return x_4;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_5, 0);
x_223 = lean_ctor_get(x_5, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_5);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_4, 0, x_224);
return x_4;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_4, 1);
lean_inc(x_225);
lean_dec(x_4);
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_5, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_228 = x_5;
} else {
 lean_dec_ref(x_5);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_225);
return x_230;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_loadLeanConfig_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_loadLeanConfig___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_loadLeanConfig___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Lean(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Lean_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
