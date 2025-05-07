// Lean compiler output
// Module: Lean.Util.FileSetupInfo
// Imports: Lean.Util.LeanOptions
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26____boxed(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26_(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonFileSetupInfo;
LEAN_EXPORT lean_object* l_Lean_instToJsonFileSetupInfo;
lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26_(lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1_spec__1(x_1, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_14, 0);
x_22 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_23 = lean_string_dec_eq(x_11, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_29; 
lean_inc(x_11);
x_24 = l_String_toName(x_11);
x_29 = l_Lean_Name_isAnonymous(x_24);
if (x_29 == 0)
{
lean_free_object(x_14);
lean_dec(x_11);
switch (lean_obj_tag(x_12)) {
case 1:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
x_25 = x_12;
goto block_28;
}
else
{
uint8_t x_31; lean_object* x_32; 
x_31 = lean_ctor_get_uint8(x_12, 0);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_32, 0, x_31);
x_25 = x_32;
goto block_28;
}
}
case 2:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_int_dec_lt(x_35, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_40 == 0)
{
lean_dec(x_35);
lean_free_object(x_12);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
goto block_8;
}
else
{
lean_object* x_41; 
x_41 = lean_nat_abs(x_35);
lean_dec(x_35);
lean_ctor_set(x_12, 0, x_41);
x_25 = x_12;
goto block_28;
}
}
else
{
lean_dec(x_36);
lean_dec(x_35);
lean_free_object(x_12);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
goto block_8;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
lean_dec(x_12);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_to_int(x_45);
x_47 = lean_int_dec_lt(x_43, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_48 == 0)
{
lean_dec(x_43);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
goto block_8;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_abs(x_43);
lean_dec(x_43);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_25 = x_50;
goto block_28;
}
}
else
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
goto block_8;
}
}
}
case 3:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_25 = x_12;
goto block_28;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_12, 0);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_25 = x_53;
goto block_28;
}
}
default: 
{
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
goto block_8;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_54 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_55 = lean_string_append(x_54, x_11);
lean_dec(x_11);
x_56 = lean_mk_string_unchecked("'", 1, 1);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_57);
return x_14;
}
block_28:
{
lean_object* x_26; 
x_26 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_16, x_24, x_25);
x_1 = x_26;
x_2 = x_13;
goto _start;
}
}
else
{
lean_free_object(x_14);
lean_dec(x_11);
switch (lean_obj_tag(x_12)) {
case 1:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
x_17 = x_12;
goto block_21;
}
else
{
uint8_t x_59; lean_object* x_60; 
x_59 = lean_ctor_get_uint8(x_12, 0);
lean_dec(x_12);
x_60 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_60, 0, x_59);
x_17 = x_60;
goto block_21;
}
}
case 2:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_to_int(x_65);
x_67 = lean_int_dec_lt(x_63, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_68 == 0)
{
lean_dec(x_63);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_13);
goto block_5;
}
else
{
lean_object* x_69; 
x_69 = lean_nat_abs(x_63);
lean_dec(x_63);
lean_ctor_set(x_12, 0, x_69);
x_17 = x_12;
goto block_21;
}
}
else
{
lean_dec(x_64);
lean_dec(x_63);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_13);
goto block_5;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_12, 0);
lean_inc(x_70);
lean_dec(x_12);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_to_int(x_73);
x_75 = lean_int_dec_lt(x_71, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = lean_nat_dec_eq(x_72, x_73);
lean_dec(x_72);
if (x_76 == 0)
{
lean_dec(x_71);
lean_dec(x_16);
lean_dec(x_13);
goto block_5;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_nat_abs(x_71);
lean_dec(x_71);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_17 = x_78;
goto block_21;
}
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_16);
lean_dec(x_13);
goto block_5;
}
}
}
case 3:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_12);
if (x_79 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_17 = x_12;
goto block_21;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_12, 0);
lean_inc(x_80);
lean_dec(x_12);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_17 = x_81;
goto block_21;
}
}
default: 
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
goto block_5;
}
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_16, x_18, x_17);
x_1 = x_19;
x_2 = x_13;
goto _start;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_14, 0);
lean_inc(x_82);
lean_dec(x_14);
x_88 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_89 = lean_string_dec_eq(x_11, x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_95; 
lean_inc(x_11);
x_90 = l_String_toName(x_11);
x_95 = l_Lean_Name_isAnonymous(x_90);
if (x_95 == 0)
{
lean_dec(x_11);
switch (lean_obj_tag(x_12)) {
case 1:
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get_uint8(x_12, 0);
if (lean_is_exclusive(x_12)) {
 x_97 = x_12;
} else {
 lean_dec_ref(x_12);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 0, 1);
} else {
 x_98 = x_97;
}
lean_ctor_set_uint8(x_98, 0, x_96);
x_91 = x_98;
goto block_94;
}
case 2:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_12, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_100 = x_12;
} else {
 lean_dec_ref(x_12);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_nat_to_int(x_103);
x_105 = lean_int_dec_lt(x_101, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = lean_nat_dec_eq(x_102, x_103);
lean_dec(x_102);
if (x_106 == 0)
{
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_13);
goto block_8;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_nat_abs(x_101);
lean_dec(x_101);
if (lean_is_scalar(x_100)) {
 x_108 = lean_alloc_ctor(2, 1, 0);
} else {
 x_108 = x_100;
}
lean_ctor_set(x_108, 0, x_107);
x_91 = x_108;
goto block_94;
}
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_13);
goto block_8;
}
}
case 3:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_12, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_110 = x_12;
} else {
 lean_dec_ref(x_12);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 1, 0);
} else {
 x_111 = x_110;
 lean_ctor_set_tag(x_111, 0);
}
lean_ctor_set(x_111, 0, x_109);
x_91 = x_111;
goto block_94;
}
default: 
{
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_13);
lean_dec(x_12);
goto block_8;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_13);
lean_dec(x_12);
x_112 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_113 = lean_string_append(x_112, x_11);
lean_dec(x_11);
x_114 = lean_mk_string_unchecked("'", 1, 1);
x_115 = lean_string_append(x_113, x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
block_94:
{
lean_object* x_92; 
x_92 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_82, x_90, x_91);
x_1 = x_92;
x_2 = x_13;
goto _start;
}
}
else
{
lean_dec(x_11);
switch (lean_obj_tag(x_12)) {
case 1:
{
uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get_uint8(x_12, 0);
if (lean_is_exclusive(x_12)) {
 x_118 = x_12;
} else {
 lean_dec_ref(x_12);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 0, 1);
} else {
 x_119 = x_118;
}
lean_ctor_set_uint8(x_119, 0, x_117);
x_83 = x_119;
goto block_87;
}
case 2:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_120 = lean_ctor_get(x_12, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_121 = x_12;
} else {
 lean_dec_ref(x_12);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_to_int(x_124);
x_126 = lean_int_dec_lt(x_122, x_125);
lean_dec(x_125);
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = lean_nat_dec_eq(x_123, x_124);
lean_dec(x_123);
if (x_127 == 0)
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_82);
lean_dec(x_13);
goto block_5;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_nat_abs(x_122);
lean_dec(x_122);
if (lean_is_scalar(x_121)) {
 x_129 = lean_alloc_ctor(2, 1, 0);
} else {
 x_129 = x_121;
}
lean_ctor_set(x_129, 0, x_128);
x_83 = x_129;
goto block_87;
}
}
else
{
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_82);
lean_dec(x_13);
goto block_5;
}
}
case 3:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_12, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_131 = x_12;
} else {
 lean_dec_ref(x_12);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 1, 0);
} else {
 x_132 = x_131;
 lean_ctor_set_tag(x_132, 0);
}
lean_ctor_set(x_132, 0, x_130);
x_83 = x_132;
goto block_87;
}
default: 
{
lean_dec(x_82);
lean_dec(x_13);
lean_dec(x_12);
goto block_5;
}
}
}
block_87:
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_box(0);
x_85 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_82, x_84, x_83);
x_1 = x_85;
x_2 = x_13;
goto _start;
}
}
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("invalid LeanOptionValue type", 28, 28);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("invalid LeanOptionValue type", 28, 28);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1_spec__1(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
x_14 = lean_unsigned_to_nat(80u);
x_15 = l_Lean_Json_pretty(x_3, x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("paths", 5, 5);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("FileSetupInfo", 13, 13);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_6);
x_12 = l_Lean_Name_toString(x_9, x_11, x_6);
x_13 = lean_mk_string_unchecked(".", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_Name_mkStr1(x_2);
x_16 = lean_unbox(x_10);
x_17 = l_Lean_Name_toString(x_15, x_16, x_6);
x_18 = lean_string_append(x_14, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked(": ", 2, 2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_21);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26____boxed), 1, 0);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("FileSetupInfo", 13, 13);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
lean_inc(x_23);
x_29 = l_Lean_Name_toString(x_26, x_28, x_23);
x_30 = lean_mk_string_unchecked(".", 1, 1);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lean_Name_mkStr1(x_2);
x_33 = lean_unbox(x_27);
x_34 = l_Lean_Name_toString(x_32, x_33, x_23);
x_35 = lean_string_append(x_31, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked(": ", 2, 2);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_string_append(x_37, x_22);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_mk_string_unchecked("setupOptions", 12, 12);
x_45 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26____boxed), 1, 0);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("FileSetupInfo", 13, 13);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
lean_inc(x_48);
x_54 = l_Lean_Name_toString(x_51, x_53, x_48);
x_55 = lean_mk_string_unchecked(".", 1, 1);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = l_Lean_Name_mkStr1(x_44);
x_58 = lean_unbox(x_52);
x_59 = l_Lean_Name_toString(x_57, x_58, x_48);
x_60 = lean_string_append(x_56, x_59);
lean_dec(x_59);
x_61 = lean_mk_string_unchecked(": ", 2, 2);
x_62 = lean_string_append(x_60, x_61);
lean_dec(x_61);
x_63 = lean_string_append(x_62, x_47);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_63);
return x_45;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_alloc_closure((void*)(l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26____boxed), 1, 0);
x_66 = lean_mk_string_unchecked("Lean", 4, 4);
x_67 = lean_mk_string_unchecked("FileSetupInfo", 13, 13);
x_68 = l_Lean_Name_mkStr2(x_66, x_67);
x_69 = lean_box(1);
x_70 = lean_unbox(x_69);
lean_inc(x_65);
x_71 = l_Lean_Name_toString(x_68, x_70, x_65);
x_72 = lean_mk_string_unchecked(".", 1, 1);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = l_Lean_Name_mkStr1(x_44);
x_75 = lean_unbox(x_69);
x_76 = l_Lean_Name_toString(x_74, x_75, x_65);
x_77 = lean_string_append(x_73, x_76);
lean_dec(x_76);
x_78 = lean_mk_string_unchecked(": ", 2, 2);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = lean_string_append(x_79, x_64);
lean_dec(x_64);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_82; 
lean_dec(x_43);
x_82 = !lean_is_exclusive(x_45);
if (x_82 == 0)
{
lean_ctor_set_tag(x_45, 0);
return x_45;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_45, 0);
lean_inc(x_83);
lean_dec(x_45);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_45);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_45, 0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_43);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_45, 0, x_87);
return x_45;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_45, 0);
lean_inc(x_88);
lean_dec(x_45);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_43);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26__spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo___lam__0____x40_Lean_Util_FileSetupInfo___hyg_26_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonFileSetupInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_FileSetupInfo_0__Lean_fromJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_26_), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0___lam__0___boxed), 1, 0);
x_8 = l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0(x_1, x_3);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_4, x_10, x_7);
switch (lean_obj_tag(x_5)) {
case 0:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; 
lean_ctor_set_tag(x_5, 3);
x_13 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_5);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_16);
x_1 = x_17;
x_2 = x_6;
goto _start;
}
}
case 1:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_5);
x_1 = x_20;
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_23, 0, x_22);
x_24 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_23);
x_1 = x_24;
x_2 = x_6;
goto _start;
}
}
default: 
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = l_Lean_JsonNumber_fromNat(x_27);
lean_ctor_set(x_5, 0, x_28);
x_29 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_5);
x_1 = x_29;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec(x_5);
x_32 = l_Lean_JsonNumber_fromNat(x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_33);
x_1 = x_34;
x_2 = x_6;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("paths", 5, 5);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55_(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("setupOptions", 12, 12);
x_10 = lean_box(0);
x_11 = l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0(x_10, x_6);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(x_17, x_19);
x_21 = l_Lean_Json_mkObj(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at_____private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132__spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToJsonFileSetupInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Util_LeanOptions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_LeanOptions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instFromJsonFileSetupInfo = _init_l_Lean_instFromJsonFileSetupInfo();
lean_mark_persistent(l_Lean_instFromJsonFileSetupInfo);
l_Lean_instToJsonFileSetupInfo = _init_l_Lean_instToJsonFileSetupInfo();
lean_mark_persistent(l_Lean_instToJsonFileSetupInfo);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
