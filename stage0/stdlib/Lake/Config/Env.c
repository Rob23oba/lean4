// Lean compiler output
// Module: Lake.Config.Env
// Imports: Lake.Util.Name Lake.Util.NativeLib Lake.Config.InstallPath
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
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_toolchain;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0___lam__0___boxed(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0___lam__0(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_noToolchainVars;
LEAN_EXPORT lean_object* l_Lake_Env_compute_computePkgUrlMap(lean_object*);
lean_object* l_Lake_getSearchPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_Env_compute_computePkgUrlMap_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_toolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
lean_object* l_Lake_envToBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
LEAN_EXPORT lean_object* l_Lake_instInhabitedEnv;
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_toolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object*);
extern uint8_t l_System_Platform_isWindows;
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
uint32_t l_Char_ofNat(lean_object*);
static lean_object* _init_l_Lake_instInhabitedEnv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_1 = lean_mk_string_unchecked("", 0, 0);
lean_inc_n(x_1, 6);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
x_3 = lean_box(0);
x_4 = l_Array_empty(lean_box(0));
lean_inc_n(x_4, 5);
lean_inc_n(x_1, 13);
x_5 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
lean_ctor_set(x_5, 6, x_1);
lean_ctor_set(x_5, 7, x_1);
lean_ctor_set(x_5, 8, x_1);
lean_ctor_set(x_5, 9, x_1);
lean_ctor_set(x_5, 10, x_1);
lean_ctor_set(x_5, 11, x_1);
lean_ctor_set(x_5, 12, x_1);
lean_ctor_set(x_5, 13, x_4);
lean_ctor_set(x_5, 14, x_4);
lean_ctor_set(x_5, 15, x_4);
lean_ctor_set(x_5, 16, x_4);
lean_ctor_set(x_5, 17, x_4);
lean_ctor_set(x_5, 18, x_4);
x_6 = lean_unbox(x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*19, x_6);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_box(0);
lean_inc_n(x_1, 2);
x_10 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_1);
lean_ctor_set(x_10, 4, x_1);
lean_ctor_set(x_10, 5, x_8);
lean_ctor_set(x_10, 6, x_1);
lean_ctor_set(x_10, 7, x_9);
lean_ctor_set(x_10, 8, x_9);
lean_ctor_set(x_10, 9, x_9);
lean_ctor_set(x_10, 10, x_9);
x_11 = lean_unbox(x_3);
lean_ctor_set_uint8(x_10, sizeof(void*)*11, x_11);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lake_Env_compute_computePkgUrlMap_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_RBNode_foldM___at___Lake_Env_compute_computePkgUrlMap_spec__0(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_12 = lean_string_dec_eq(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_5);
x_13 = l_String_toName(x_5);
x_14 = l_Lean_Name_isAnonymous(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_8);
lean_dec(x_5);
x_15 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_10, x_13, x_19);
x_1 = x_20;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_23 = lean_string_append(x_22, x_5);
lean_dec(x_5);
x_24 = lean_mk_string_unchecked("'", 1, 1);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
}
else
{
lean_object* x_26; 
lean_free_object(x_8);
lean_dec(x_5);
x_26 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_10, x_31, x_30);
x_1 = x_32;
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_36 = lean_string_dec_eq(x_5, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_5);
x_37 = l_String_toName(x_5);
x_38 = l_Lean_Name_isAnonymous(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_5);
x_39 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_34, x_37, x_43);
x_1 = x_44;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
x_46 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_47 = lean_string_append(x_46, x_5);
lean_dec(x_5);
x_48 = lean_mk_string_unchecked("'", 1, 1);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_5);
x_51 = l_Lean_Json_getStr_x3f(x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
lean_dec(x_7);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_34, x_56, x_55);
x_1 = x_57;
x_2 = x_7;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute_computePkgUrlMap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_mk_string_unchecked("LAKE_PKG_URL_MAP", 16, 16);
x_3 = lean_io_getenv(x_2, x_1);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_Json_parse(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_7 = x_16;
goto block_11;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = l_Lean_RBNode_foldM___at___Lake_Env_compute_computePkgUrlMap_spec__0(x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_7 = x_21;
goto block_11;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
x_25 = lean_unsigned_to_nat(80u);
x_26 = l_Lean_Json_pretty(x_17, x_25);
x_27 = lean_string_append(x_24, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("'", 1, 1);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_7 = x_29;
goto block_11;
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_mk_string_unchecked("'LAKE_PKG_URL_MAP' has invalid JSON: ", 37, 37);
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
if (lean_is_scalar(x_6)) {
 x_10 = lean_alloc_ctor(1, 2, 0);
} else {
 x_10 = x_6;
 lean_ctor_set_tag(x_10, 1);
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_mk_string_unchecked("RESERVOIR_API_BASE_URL", 22, 22);
x_98 = lean_io_getenv(x_97, x_5);
lean_dec(x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_129; 
x_129 = lean_mk_string_unchecked("https://reservoir.lean-lang.org/api", 35, 35);
x_101 = x_129;
goto block_128;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint32_t x_133; lean_object* x_134; uint32_t x_135; uint8_t x_136; 
x_130 = lean_ctor_get(x_99, 0);
lean_inc(x_130);
lean_dec(x_99);
x_131 = lean_string_utf8_byte_size(x_130);
x_132 = lean_string_utf8_prev(x_130, x_131);
x_133 = lean_string_utf8_get(x_130, x_132);
lean_dec(x_132);
x_134 = lean_unsigned_to_nat(47u);
x_135 = l_Char_ofNat(x_134);
x_136 = l_instDecidableEqChar(x_133, x_135);
if (x_136 == 0)
{
lean_dec(x_131);
x_101 = x_130;
goto block_128;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_unsigned_to_nat(0u);
lean_inc(x_131);
lean_inc(x_130);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_131);
x_140 = l_Substring_prevn(x_139, x_137, x_131);
lean_dec(x_139);
x_141 = lean_string_utf8_extract(x_130, x_138, x_140);
lean_dec(x_140);
lean_dec(x_130);
x_101 = x_141;
goto block_128;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_6);
lean_ctor_set(x_16, 5, x_8);
lean_ctor_set(x_16, 6, x_15);
lean_ctor_set(x_16, 7, x_13);
lean_ctor_set(x_16, 8, x_12);
lean_ctor_set(x_16, 9, x_11);
lean_ctor_set(x_16, 10, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*11, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
block_31:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_29; 
x_29 = lean_mk_string_unchecked("", 0, 0);
x_6 = x_19;
x_7 = x_28;
x_8 = x_20;
x_9 = x_22;
x_10 = x_21;
x_11 = x_23;
x_12 = x_25;
x_13 = x_27;
x_14 = x_26;
x_15 = x_29;
goto block_18;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_6 = x_19;
x_7 = x_28;
x_8 = x_20;
x_9 = x_22;
x_10 = x_21;
x_11 = x_23;
x_12 = x_25;
x_13 = x_27;
x_14 = x_26;
x_15 = x_30;
goto block_18;
}
}
block_43:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_19 = x_32;
x_20 = x_33;
x_21 = x_35;
x_22 = x_34;
x_23 = x_36;
x_24 = x_38;
x_25 = x_37;
x_26 = x_40;
x_27 = x_39;
x_28 = x_42;
goto block_31;
}
block_60:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_45) == 0)
{
x_32 = x_53;
x_33 = x_44;
x_34 = x_46;
x_35 = x_47;
x_36 = x_48;
x_37 = x_49;
x_38 = x_50;
x_39 = x_51;
x_40 = x_52;
goto block_43;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
lean_dec(x_45);
x_55 = l_Lake_envToBool_x3f(x_54);
if (lean_obj_tag(x_55) == 0)
{
x_32 = x_53;
x_33 = x_44;
x_34 = x_46;
x_35 = x_47;
x_36 = x_48;
x_37 = x_49;
x_38 = x_50;
x_39 = x_51;
x_40 = x_52;
goto block_43;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
x_19 = x_53;
x_20 = x_44;
x_21 = x_47;
x_22 = x_46;
x_23 = x_48;
x_24 = x_50;
x_25 = x_49;
x_26 = x_52;
x_27 = x_51;
x_28 = x_57;
goto block_31;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_45);
x_58 = lean_ctor_get(x_4, 0);
lean_inc(x_58);
lean_dec(x_4);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
x_19 = x_53;
x_20 = x_44;
x_21 = x_47;
x_22 = x_46;
x_23 = x_48;
x_24 = x_50;
x_25 = x_49;
x_26 = x_52;
x_27 = x_51;
x_28 = x_59;
goto block_31;
}
}
block_96:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_64 = lean_mk_string_unchecked("LAKE_NO_CACHE", 13, 13);
x_65 = lean_io_getenv(x_64, x_63);
lean_dec(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_mk_string_unchecked("LEAN_GITHASH", 12, 12);
x_69 = lean_io_getenv(x_68, x_67);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_mk_string_unchecked("ELAN_TOOLCHAIN", 14, 14);
x_73 = lean_io_getenv(x_72, x_71);
lean_dec(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
x_77 = l_Lake_getSearchPath(x_76, x_75);
lean_dec(x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
x_81 = l_Lake_getSearchPath(x_80, x_79);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lake_sharedLibPathEnvVar;
x_85 = l_Lake_getSearchPath(x_84, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_mk_string_unchecked("PATH", 4, 4);
x_89 = l_Lake_getSearchPath(x_88, x_87);
lean_dec(x_88);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_mk_string_unchecked("", 0, 0);
x_44 = x_61;
x_45 = x_66;
x_46 = x_91;
x_47 = x_90;
x_48 = x_86;
x_49 = x_82;
x_50 = x_74;
x_51 = x_78;
x_52 = x_62;
x_53 = x_92;
goto block_60;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_ctor_get(x_70, 0);
lean_inc(x_95);
lean_dec(x_70);
x_44 = x_61;
x_45 = x_66;
x_46 = x_94;
x_47 = x_93;
x_48 = x_86;
x_49 = x_82;
x_50 = x_74;
x_51 = x_78;
x_52 = x_62;
x_53 = x_95;
goto block_60;
}
}
block_128:
{
lean_object* x_102; 
x_102 = l_Lake_Env_compute_computePkgUrlMap(x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_mk_string_unchecked("RESERVOIR_API_URL", 17, 17);
x_106 = lean_io_getenv(x_105, x_104);
lean_dec(x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_mk_string_unchecked("/v1", 3, 3);
x_110 = lean_string_append(x_101, x_109);
lean_dec(x_109);
x_61 = x_103;
x_62 = x_110;
x_63 = x_108;
goto block_96;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint32_t x_115; lean_object* x_116; uint32_t x_117; uint8_t x_118; 
lean_dec(x_101);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_string_utf8_byte_size(x_112);
x_114 = lean_string_utf8_prev(x_112, x_113);
x_115 = lean_string_utf8_get(x_112, x_114);
lean_dec(x_114);
x_116 = lean_unsigned_to_nat(47u);
x_117 = l_Char_ofNat(x_116);
x_118 = l_instDecidableEqChar(x_115, x_117);
if (x_118 == 0)
{
lean_dec(x_113);
x_61 = x_103;
x_62 = x_112;
x_63 = x_111;
goto block_96;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_unsigned_to_nat(0u);
lean_inc(x_113);
lean_inc(x_112);
x_121 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_113);
x_122 = l_Substring_prevn(x_121, x_119, x_113);
lean_dec(x_121);
x_123 = lean_string_utf8_extract(x_112, x_120, x_122);
lean_dec(x_122);
lean_dec(x_112);
x_61 = x_103;
x_62 = x_123;
x_63 = x_111;
goto block_96;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_101);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_102);
if (x_124 == 0)
{
return x_102;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_102, 0);
x_126 = lean_ctor_get(x_102, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_102);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_instDecidableEqPos(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanGithash___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanGithash(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_toolchain(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_instDecidableEqPos(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_toolchain;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_toolchain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_toolchain(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 6);
x_6 = lean_string_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 10);
lean_inc(x_7);
lean_inc(x_5);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_inc(x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 10);
lean_inc(x_10);
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_path___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_path(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 8);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanSrcPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_sharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lake_LeanInstall_sharedLibPath(x_2);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 9);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_appendTR(lean_box(0), x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Env_noToolchainVars() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("ELAN_TOOLCHAIN", 14, 14);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_mk_string_unchecked("LAKE", 4, 4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_mk_string_unchecked("LAKE_OVERRIDE_LEAN", 18, 18);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_mk_string_unchecked("LAKE_HOME", 9, 9);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_mk_string_unchecked("LEAN", 4, 4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_mk_string_unchecked("LEAN_GITHASH", 12, 12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_mk_string_unchecked("LEAN_AR", 7, 7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_array_push(x_19, x_3);
x_21 = lean_array_push(x_20, x_5);
x_22 = lean_array_push(x_21, x_7);
x_23 = lean_array_push(x_22, x_9);
x_24 = lean_array_push(x_23, x_11);
x_25 = lean_array_push(x_24, x_13);
x_26 = lean_array_push(x_25, x_15);
x_27 = lean_array_push(x_26, x_17);
return x_27;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0___lam__0___boxed), 1, 0);
x_8 = l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0(x_1, x_3);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_4, x_10, x_7);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_13 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_baseVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_mk_string_unchecked("ELAN", 4, 4);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_83; 
x_83 = lean_box(0);
x_72 = x_83;
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_71, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_72 = x_86;
goto block_82;
}
block_57:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_6 = lean_mk_string_unchecked("LAKE", 4, 4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 5);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("LAKE_HOME", 9, 9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_mk_string_unchecked("LAKE_PKG_URL_MAP", 16, 16);
x_18 = lean_box(0);
x_19 = l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0(x_18, x_13);
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Json_compress(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("LEAN", 4, 4);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 7);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("LEAN_GITHASH", 12, 12);
x_30 = l_Lake_Env_leanGithash(x_1);
lean_dec(x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("LEAN_AR", 7, 7);
x_38 = lean_ctor_get(x_25, 11);
lean_inc(x_38);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked("LEAN_CC", 7, 7);
x_42 = l_Lake_LeanInstall_leanCc_x3f(x_25);
lean_dec(x_25);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(11u);
x_45 = lean_mk_empty_array_with_capacity(x_44);
x_46 = lean_array_push(x_45, x_3);
x_47 = lean_array_push(x_46, x_2);
x_48 = lean_array_push(x_47, x_14);
x_49 = lean_array_push(x_48, x_15);
x_50 = lean_array_push(x_49, x_16);
x_51 = lean_array_push(x_50, x_23);
x_52 = lean_array_push(x_51, x_28);
x_53 = lean_array_push(x_52, x_32);
x_54 = lean_array_push(x_53, x_36);
x_55 = lean_array_push(x_54, x_40);
x_56 = lean_array_push(x_55, x_43);
return x_56;
}
block_69:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_mk_string_unchecked("ELAN_TOOLCHAIN", 14, 14);
x_63 = l_Lake_Env_toolchain(x_1);
x_64 = lean_string_utf8_byte_size(x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_instDecidableEqPos(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_63);
x_2 = x_61;
x_3 = x_59;
x_4 = x_62;
x_5 = x_67;
goto block_57;
}
else
{
lean_object* x_68; 
lean_dec(x_63);
x_68 = lean_box(0);
x_2 = x_61;
x_3 = x_59;
x_4 = x_62;
x_5 = x_68;
goto block_57;
}
}
block_82:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked("ELAN_HOME", 9, 9);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_58 = x_74;
x_59 = x_73;
x_60 = x_75;
goto block_69;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
lean_ctor_set(x_71, 0, x_78);
x_58 = x_74;
x_59 = x_73;
x_60 = x_71;
goto block_69;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_71, 0);
lean_inc(x_79);
lean_dec(x_71);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_58 = x_74;
x_59 = x_73;
x_60 = x_81;
goto block_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at___Lake_Env_baseVars_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_vars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_1);
x_2 = l_Lake_Env_baseVars(x_1);
x_3 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
x_4 = l_Lake_Env_leanPath(x_1);
x_5 = l_System_SearchPath_toString(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
x_9 = l_Lake_Env_leanSrcPath(x_1);
x_10 = l_System_SearchPath_toString(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("PATH", 4, 4);
x_14 = l_Lake_Env_path(x_1);
x_15 = l_System_SearchPath_toString(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_mk_empty_array_with_capacity(x_18);
x_20 = lean_array_push(x_19, x_7);
x_21 = lean_array_push(x_20, x_12);
x_22 = lean_array_push(x_21, x_17);
x_23 = l_Array_append(lean_box(0), x_2, x_22);
lean_dec(x_22);
x_24 = l_System_Platform_isWindows;
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Lake_sharedLibPathEnvVar;
x_26 = l_Lake_Env_sharedLibPath(x_1);
x_27 = l_System_SearchPath_toString(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_23, x_29);
return x_30;
}
else
{
lean_dec(x_1);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 3);
x_6 = l_Lake_Env_leanPath(x_1);
lean_inc(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Env_leanSearchPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Env_leanSearchPath(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_InstallPath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InstallPath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedEnv = _init_l_Lake_instInhabitedEnv();
lean_mark_persistent(l_Lake_instInhabitedEnv);
l_Lake_Env_noToolchainVars = _init_l_Lake_Env_noToolchainVars();
lean_mark_persistent(l_Lake_Env_noToolchainVars);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
