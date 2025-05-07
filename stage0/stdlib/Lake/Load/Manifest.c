// Lean compiler output
// Module: Lake.Load.Manifest
// Imports: Lake.Util.Log Lake.Util.Name Lake.Util.FilePath Lake.Util.JsonObject Lake.Util.Version Lake.Config.Defaults
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
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instToJson;
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456_(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntrySrc;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_115_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_instFromJson;
lean_object* l_Lake_StdVer_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_toJson_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_instFromJson;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_toJson_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntry;
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_115____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonPackageEntryV6;
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_instToJson;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lake_StdVer_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonPackageEntryV6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__2(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lake_StdVer_compare___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_115____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_115_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_version;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(size_t, size_t, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageEntryV6;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
uint32_t l_Char_ofNat(lean_object*);
static lean_object* _init_l_Lake_Manifest_version() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
x_4 = lean_mk_string_unchecked("", 0, 0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(x_1, x_4);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_115_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_115_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_mk_string_unchecked("git", 3, 3);
x_25 = lean_unsigned_to_nat(7u);
x_26 = lean_mk_string_unchecked("url", 3, 3);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("rev", 3, 3);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_mk_string_unchecked("inputRev\?", 9, 9);
x_31 = l_Lean_Name_mkStr1(x_30);
x_32 = lean_mk_string_unchecked("subDir\?", 7, 7);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_mk_empty_array_with_capacity(x_25);
x_35 = lean_array_push(x_34, x_1);
x_36 = lean_array_push(x_35, x_2);
x_37 = lean_array_push(x_36, x_3);
x_38 = lean_array_push(x_37, x_27);
x_39 = lean_array_push(x_38, x_29);
x_40 = lean_array_push(x_39, x_31);
x_41 = lean_array_push(x_40, x_33);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_Json_parseTagged(x_4, x_24, x_25, x_42);
lean_dec(x_42);
lean_dec(x_24);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Except_orElseLazy___redArg(x_43, x_5);
lean_dec(x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Except_orElseLazy___redArg(x_47, x_5);
lean_dec(x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_69; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
 x_50 = lean_box(0);
}
x_172 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_173 = lean_array_get(x_6, x_49, x_172);
lean_inc(x_173);
x_174 = l_Lean_Json_getStr_x3f(x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
lean_dec(x_173);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_6);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec(x_174);
x_9 = x_175;
goto block_12;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_178 = lean_string_dec_eq(x_176, x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = l_String_toName(x_176);
x_180 = l_Lean_Name_isAnonymous(x_179);
if (x_180 == 0)
{
lean_dec(x_173);
x_69 = x_179;
goto block_171;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_179);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_6);
x_181 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_182 = lean_unsigned_to_nat(80u);
x_183 = l_Lean_Json_pretty(x_173, x_182);
x_184 = lean_string_append(x_181, x_183);
lean_dec(x_183);
x_185 = lean_mk_string_unchecked("'", 1, 1);
x_186 = lean_string_append(x_184, x_185);
lean_dec(x_185);
x_9 = x_186;
goto block_12;
}
}
else
{
lean_object* x_187; 
lean_dec(x_176);
lean_dec(x_173);
x_187 = lean_box(0);
x_69 = x_187;
goto block_171;
}
}
block_68:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_unsigned_to_nat(6u);
x_58 = lean_array_get(x_6, x_49, x_57);
lean_dec(x_49);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_13 = x_51;
x_14 = x_52;
x_15 = x_53;
x_16 = x_56;
x_17 = x_55;
x_18 = x_54;
x_19 = x_59;
goto block_23;
}
else
{
lean_object* x_60; 
x_60 = l_Lean_Json_getStr_x3f(x_58);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Except_orElseLazy___redArg(x_60, x_5);
lean_dec(x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Except_orElseLazy___redArg(x_64, x_5);
lean_dec(x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_13 = x_51;
x_14 = x_52;
x_15 = x_53;
x_16 = x_56;
x_17 = x_55;
x_18 = x_54;
x_19 = x_67;
goto block_23;
}
}
}
block_171:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_unsigned_to_nat(1u);
lean_inc(x_6);
x_71 = lean_array_get(x_6, x_49, x_70);
if (lean_obj_tag(x_71) == 5)
{
uint8_t x_72; 
lean_dec(x_50);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_box(0);
x_75 = l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(x_74, x_73);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_free_object(x_71);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = l_Except_orElseLazy___redArg(x_75, x_5);
lean_dec(x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Except_orElseLazy___redArg(x_79, x_5);
lean_dec(x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_unsigned_to_nat(2u);
lean_inc(x_6);
x_83 = lean_array_get(x_6, x_49, x_82);
x_84 = l_Lean_Json_getBool_x3f(x_83);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_dec(x_81);
lean_free_object(x_71);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = l_Except_orElseLazy___redArg(x_84, x_5);
lean_dec(x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Except_orElseLazy___redArg(x_88, x_5);
lean_dec(x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
lean_dec(x_84);
x_91 = lean_unsigned_to_nat(3u);
lean_inc(x_6);
x_92 = lean_array_get(x_6, x_49, x_91);
x_93 = l_Lean_Json_getStr_x3f(x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
lean_dec(x_90);
lean_dec(x_81);
lean_free_object(x_71);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Except_orElseLazy___redArg(x_93, x_5);
lean_dec(x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Except_orElseLazy___redArg(x_97, x_5);
lean_dec(x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
lean_dec(x_93);
lean_inc(x_6);
x_100 = lean_array_get(x_6, x_49, x_7);
x_101 = l_Lean_Json_getStr_x3f(x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
lean_dec(x_99);
lean_dec(x_90);
lean_dec(x_81);
lean_free_object(x_71);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Except_orElseLazy___redArg(x_101, x_5);
lean_dec(x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Except_orElseLazy___redArg(x_105, x_5);
lean_dec(x_105);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
lean_dec(x_101);
x_108 = lean_unsigned_to_nat(5u);
lean_inc(x_6);
x_109 = lean_array_get(x_6, x_49, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
lean_free_object(x_71);
x_110 = lean_box(0);
x_111 = lean_unbox(x_90);
lean_dec(x_90);
x_51 = x_99;
x_52 = x_69;
x_53 = x_111;
x_54 = x_81;
x_55 = x_107;
x_56 = x_110;
goto block_68;
}
else
{
lean_object* x_112; 
x_112 = l_Lean_Json_getStr_x3f(x_109);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
lean_dec(x_107);
lean_dec(x_99);
lean_dec(x_90);
lean_dec(x_81);
lean_free_object(x_71);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = l_Except_orElseLazy___redArg(x_112, x_5);
lean_dec(x_112);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Except_orElseLazy___redArg(x_116, x_5);
lean_dec(x_116);
return x_117;
}
}
else
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_112, 0);
lean_inc(x_118);
lean_dec(x_112);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_118);
x_119 = lean_unbox(x_90);
lean_dec(x_90);
x_51 = x_99;
x_52 = x_69;
x_53 = x_119;
x_54 = x_81;
x_55 = x_107;
x_56 = x_71;
goto block_68;
}
}
}
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_71, 0);
lean_inc(x_120);
lean_dec(x_71);
x_121 = lean_box(0);
x_122 = l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(x_121, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
x_126 = l_Except_orElseLazy___redArg(x_125, x_5);
lean_dec(x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
lean_dec(x_122);
x_128 = lean_unsigned_to_nat(2u);
lean_inc(x_6);
x_129 = lean_array_get(x_6, x_49, x_128);
x_130 = l_Lean_Json_getBool_x3f(x_129);
lean_dec(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_127);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
x_134 = l_Except_orElseLazy___redArg(x_133, x_5);
lean_dec(x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
lean_dec(x_130);
x_136 = lean_unsigned_to_nat(3u);
lean_inc(x_6);
x_137 = lean_array_get(x_6, x_49, x_136);
x_138 = l_Lean_Json_getStr_x3f(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_135);
lean_dec(x_127);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 1, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_139);
x_142 = l_Except_orElseLazy___redArg(x_141, x_5);
lean_dec(x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_138, 0);
lean_inc(x_143);
lean_dec(x_138);
lean_inc(x_6);
x_144 = lean_array_get(x_6, x_49, x_7);
x_145 = l_Lean_Json_getStr_x3f(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_127);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
x_149 = l_Except_orElseLazy___redArg(x_148, x_5);
lean_dec(x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
lean_dec(x_145);
x_151 = lean_unsigned_to_nat(5u);
lean_inc(x_6);
x_152 = lean_array_get(x_6, x_49, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_box(0);
x_154 = lean_unbox(x_135);
lean_dec(x_135);
x_51 = x_143;
x_52 = x_69;
x_53 = x_154;
x_54 = x_127;
x_55 = x_150;
x_56 = x_153;
goto block_68;
}
else
{
lean_object* x_155; 
x_155 = l_Lean_Json_getStr_x3f(x_152);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_150);
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_127);
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
x_159 = l_Except_orElseLazy___redArg(x_158, x_5);
lean_dec(x_158);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_155, 0);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_unbox(x_135);
lean_dec(x_135);
x_51 = x_143;
x_52 = x_69;
x_53 = x_162;
x_54 = x_127;
x_55 = x_150;
x_56 = x_161;
goto block_68;
}
}
}
}
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_69);
lean_dec(x_49);
lean_dec(x_6);
x_163 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
x_164 = lean_unsigned_to_nat(80u);
x_165 = l_Lean_Json_pretty(x_71, x_164);
x_166 = lean_string_append(x_163, x_165);
lean_dec(x_165);
x_167 = lean_mk_string_unchecked("'", 1, 1);
x_168 = lean_string_append(x_166, x_167);
lean_dec(x_167);
if (lean_is_scalar(x_50)) {
 x_169 = lean_alloc_ctor(0, 1, 0);
} else {
 x_169 = x_50;
 lean_ctor_set_tag(x_169, 0);
}
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Except_orElseLazy___redArg(x_169, x_5);
lean_dec(x_169);
return x_170;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Except_orElseLazy___redArg(x_10, x_5);
lean_dec(x_10);
return x_11;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_alloc_ctor(1, 6, 1);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Except_orElseLazy___redArg(x_21, x_5);
lean_dec(x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_115____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("path", 4, 4);
x_5 = lean_unsigned_to_nat(4u);
x_6 = lean_mk_string_unchecked("name", 4, 4);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("opts", 4, 4);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("inherited", 9, 9);
x_11 = l_Lean_Name_mkStr1(x_10);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_115____boxed), 8, 7);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_1);
lean_closure_set(x_12, 4, x_2);
lean_closure_set(x_12, 5, x_3);
lean_closure_set(x_12, 6, x_5);
x_17 = lean_mk_string_unchecked("dir", 3, 3);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_empty_array_with_capacity(x_5);
x_20 = lean_array_push(x_19, x_7);
x_21 = lean_array_push(x_20, x_9);
x_22 = lean_array_push(x_21, x_11);
x_23 = lean_array_push(x_22, x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_24);
lean_dec(x_24);
lean_dec(x_4);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Except_orElseLazy___redArg(x_25, x_12);
lean_dec(x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Except_orElseLazy___redArg(x_29, x_12);
lean_dec(x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_array_get(x_3, x_31, x_81);
lean_inc(x_82);
x_83 = l_Lean_Json_getStr_x3f(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
lean_dec(x_82);
lean_dec(x_32);
lean_dec(x_31);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_13 = x_84;
goto block_16;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_87 = lean_string_dec_eq(x_85, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = l_String_toName(x_85);
x_89 = l_Lean_Name_isAnonymous(x_88);
if (x_89 == 0)
{
lean_dec(x_82);
x_33 = x_88;
goto block_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_88);
lean_dec(x_32);
lean_dec(x_31);
x_90 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_91 = lean_unsigned_to_nat(80u);
x_92 = l_Lean_Json_pretty(x_82, x_91);
x_93 = lean_string_append(x_90, x_92);
lean_dec(x_92);
x_94 = lean_mk_string_unchecked("'", 1, 1);
x_95 = lean_string_append(x_93, x_94);
lean_dec(x_94);
x_13 = x_95;
goto block_16;
}
}
else
{
lean_object* x_96; 
lean_dec(x_85);
lean_dec(x_82);
x_96 = lean_box(0);
x_33 = x_96;
goto block_80;
}
}
block_80:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_array_get(x_3, x_31, x_34);
if (lean_obj_tag(x_35) == 5)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = l_Lean_RBNode_foldM___at_____private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115__spec__0(x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_33);
lean_dec(x_31);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Except_orElseLazy___redArg(x_38, x_12);
lean_dec(x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Except_orElseLazy___redArg(x_42, x_12);
lean_dec(x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_array_get(x_3, x_31, x_45);
x_47 = l_Lean_Json_getBool_x3f(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_44);
lean_dec(x_33);
lean_dec(x_31);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Except_orElseLazy___redArg(x_47, x_12);
lean_dec(x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Except_orElseLazy___redArg(x_51, x_12);
lean_dec(x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_array_get(x_3, x_31, x_54);
lean_dec(x_31);
x_56 = l_Lean_Json_getStr_x3f(x_55);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_53);
lean_dec(x_44);
lean_dec(x_33);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = l_Except_orElseLazy___redArg(x_56, x_12);
lean_dec(x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Except_orElseLazy___redArg(x_60, x_12);
lean_dec(x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_56);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_56, 0);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_33);
lean_ctor_set(x_64, 1, x_44);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_unbox(x_53);
lean_dec(x_53);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_65);
lean_ctor_set(x_56, 0, x_64);
x_66 = l_Except_orElseLazy___redArg(x_56, x_12);
lean_dec(x_56);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_68, 0, x_33);
lean_ctor_set(x_68, 1, x_44);
lean_ctor_set(x_68, 2, x_67);
x_69 = lean_unbox(x_53);
lean_dec(x_53);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_69);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_68);
x_71 = l_Except_orElseLazy___redArg(x_70, x_12);
lean_dec(x_70);
return x_71;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_33);
lean_dec(x_31);
x_72 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
x_73 = lean_unsigned_to_nat(80u);
x_74 = l_Lean_Json_pretty(x_35, x_73);
x_75 = lean_string_append(x_72, x_74);
lean_dec(x_74);
x_76 = lean_mk_string_unchecked("'", 1, 1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
if (lean_is_scalar(x_32)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_32;
 lean_ctor_set_tag(x_78, 0);
}
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Except_orElseLazy___redArg(x_78, x_12);
lean_dec(x_78);
return x_79;
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Except_orElseLazy___redArg(x_14, x_12);
lean_dec(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_115____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_115_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_115____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6___lam__1____x40_Lake_Load_Manifest___hyg_115_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_instFromJsonPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0___lam__0___boxed), 1, 0);
x_8 = l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0(x_1, x_3);
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
LEAN_EXPORT uint8_t l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("name", 4, 4);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Name_toString(x_2, x_9, x_6);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("path", 4, 4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_mk_string_unchecked("opts", 4, 4);
x_15 = lean_box(0);
x_16 = l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0(x_15, x_3);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("inherited", 9, 9);
x_20 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_20, 0, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("dir", 3, 3);
x_23 = l_Lake_mkRelPathString(x_5);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Json_mkObj(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = l_Lean_Json_mkObj(x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_81; lean_object* x_82; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 5);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456____boxed), 1, 0);
x_43 = lean_mk_string_unchecked("name", 4, 4);
x_44 = lean_box(1);
x_45 = lean_unbox(x_44);
x_46 = l_Lean_Name_toString(x_35, x_45, x_42);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_mk_string_unchecked("git", 3, 3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_mk_string_unchecked("opts", 4, 4);
x_51 = lean_box(0);
x_52 = l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0(x_51, x_36);
x_53 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("inherited", 9, 9);
x_56 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_56, 0, x_37);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("url", 3, 3);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_38);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("rev", 3, 3);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_39);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_81 = lean_mk_string_unchecked("inputRev\?", 9, 9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_82 = x_93;
goto block_92;
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_40);
if (x_94 == 0)
{
lean_ctor_set_tag(x_40, 3);
x_82 = x_40;
goto block_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_40, 0);
lean_inc(x_95);
lean_dec(x_40);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_82 = x_96;
goto block_92;
}
}
block_80:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_57);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_49);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Json_mkObj(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_48);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_68);
x_79 = l_Lean_Json_mkObj(x_78);
return x_79;
}
block_92:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("subDir\?", 7, 7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_85; 
x_85 = lean_box(0);
x_64 = x_84;
x_65 = x_83;
x_66 = x_85;
goto block_80;
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_41);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_41, 0);
x_88 = l_Lake_mkRelPathString(x_87);
lean_ctor_set_tag(x_41, 3);
lean_ctor_set(x_41, 0, x_88);
x_64 = x_84;
x_65 = x_83;
x_66 = x_41;
goto block_80;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_41, 0);
lean_inc(x_89);
lean_dec(x_41);
x_90 = l_Lake_mkRelPathString(x_89);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_64 = x_84;
x_65 = x_83;
x_66 = x_91;
goto block_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at_____private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456__spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonPackageEntryV6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_456_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntryV6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("", 0, 0);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unbox(x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntrySrc() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_box(0);
x_4 = lean_box(0);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_7);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_114; 
x_37 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456____boxed), 1, 0);
x_38 = lean_mk_string_unchecked("name", 4, 4);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_box(1);
x_41 = lean_unbox(x_40);
x_42 = l_Lean_Name_toString(x_39, x_41, x_37);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("scope", 5, 5);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked("configFile", 10, 10);
x_50 = lean_ctor_get(x_1, 2);
lean_inc(x_50);
x_51 = l_Lake_mkRelPathString(x_50);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("manifestFile", 12, 12);
x_114 = lean_ctor_get(x_1, 3);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_box(0);
x_55 = x_115;
goto block_113;
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_114);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_114, 0);
x_118 = l_Lake_mkRelPathString(x_117);
lean_ctor_set_tag(x_114, 3);
lean_ctor_set(x_114, 0, x_118);
x_55 = x_114;
goto block_113;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
lean_dec(x_114);
x_120 = l_Lake_mkRelPathString(x_119);
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_55 = x_121;
goto block_113;
}
}
block_18:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_appendTR(lean_box(0), x_7, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
block_36:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("subDir", 6, 6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_2 = x_21;
x_3 = x_22;
x_4 = x_27;
x_5 = x_28;
x_6 = x_23;
x_7 = x_24;
x_8 = x_25;
x_9 = x_29;
goto block_18;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = l_Lake_mkRelPathString(x_31);
lean_ctor_set_tag(x_20, 3);
lean_ctor_set(x_20, 0, x_32);
x_2 = x_21;
x_3 = x_22;
x_4 = x_27;
x_5 = x_28;
x_6 = x_23;
x_7 = x_24;
x_8 = x_25;
x_9 = x_20;
goto block_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = l_Lake_mkRelPathString(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_2 = x_21;
x_3 = x_22;
x_4 = x_27;
x_5 = x_28;
x_6 = x_23;
x_7 = x_24;
x_8 = x_25;
x_9 = x_35;
goto block_18;
}
}
}
block_113:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_mk_string_unchecked("inherited", 9, 9);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_59 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_44);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_ctor_get(x_1, 4);
lean_inc(x_67);
lean_dec(x_1);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_mk_string_unchecked("type", 4, 4);
x_71 = lean_mk_string_unchecked("path", 4, 4);
lean_ctor_set_tag(x_67, 3);
lean_ctor_set(x_67, 0, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_67);
x_73 = lean_mk_string_unchecked("dir", 3, 3);
x_74 = l_Lake_mkRelPathString(x_69);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_61);
x_78 = l_List_appendTR(lean_box(0), x_66, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Json_mkObj(x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_67, 0);
lean_inc(x_81);
lean_dec(x_67);
x_82 = lean_mk_string_unchecked("type", 4, 4);
x_83 = lean_mk_string_unchecked("path", 4, 4);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_mk_string_unchecked("dir", 3, 3);
x_87 = l_Lake_mkRelPathString(x_81);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_61);
x_91 = l_List_appendTR(lean_box(0), x_66, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Json_mkObj(x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_94 = lean_ctor_get(x_67, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_67, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_67, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_67, 3);
lean_inc(x_97);
lean_dec(x_67);
x_98 = lean_mk_string_unchecked("type", 4, 4);
x_99 = lean_mk_string_unchecked("git", 3, 3);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_mk_string_unchecked("url", 3, 3);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_94);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_mk_string_unchecked("rev", 3, 3);
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_95);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked("inputRev", 8, 8);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_109; 
x_109 = lean_box(0);
x_19 = x_108;
x_20 = x_97;
x_21 = x_101;
x_22 = x_104;
x_23 = x_61;
x_24 = x_66;
x_25 = x_107;
x_26 = x_109;
goto block_36;
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_96);
if (x_110 == 0)
{
lean_ctor_set_tag(x_96, 3);
x_19 = x_108;
x_20 = x_97;
x_21 = x_101;
x_22 = x_104;
x_23 = x_61;
x_24 = x_66;
x_25 = x_107;
x_26 = x_96;
goto block_36;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_96, 0);
lean_inc(x_111);
lean_dec(x_96);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_19 = x_108;
x_20 = x_97;
x_21 = x_101;
x_22 = x_104;
x_23 = x_61;
x_24 = x_66;
x_25 = x_107;
x_26 = x_112;
goto block_36;
}
}
}
}
}
}
static lean_object* _init_l_Lake_PackageEntry_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_PackageEntry_toJson), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("package entry: ", 15, 15);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_23; lean_object* x_27; lean_object* x_31; 
x_31 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
lean_ctor_set_tag(x_31, 0);
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_176; lean_object* x_177; lean_object* x_210; lean_object* x_213; lean_object* x_228; lean_object* x_229; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_42 = x_31;
} else {
 lean_dec_ref(x_31);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456____boxed), 1, 0);
x_228 = lean_mk_string_unchecked("name", 4, 4);
x_229 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_228);
lean_dec(x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
x_230 = lean_mk_string_unchecked("property not found: name", 24, 24);
x_23 = x_230;
goto block_26;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_231);
x_232 = l_Lean_Json_getStr_x3f(x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
lean_dec(x_231);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec(x_232);
x_27 = x_233;
goto block_30;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_236 = lean_string_dec_eq(x_234, x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; uint8_t x_238; 
x_237 = l_String_toName(x_234);
x_238 = l_Lean_Name_isAnonymous(x_237);
if (x_238 == 0)
{
lean_dec(x_231);
x_213 = x_237;
goto block_227;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_237);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
x_239 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_240 = lean_unsigned_to_nat(80u);
x_241 = l_Lean_Json_pretty(x_231, x_240);
x_242 = lean_string_append(x_239, x_241);
lean_dec(x_241);
x_243 = lean_mk_string_unchecked("'", 1, 1);
x_244 = lean_string_append(x_242, x_243);
lean_dec(x_243);
x_27 = x_244;
goto block_30;
}
}
else
{
lean_object* x_245; 
lean_dec(x_234);
lean_dec(x_231);
x_245 = lean_box(0);
x_213 = x_245;
goto block_227;
}
}
}
block_55:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_mk_string_unchecked("package entry '", 15, 15);
x_47 = lean_box(1);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Name_toString(x_44, x_48, x_43);
x_50 = lean_string_append(x_46, x_49);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("': ", 3, 3);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
x_53 = lean_string_append(x_52, x_45);
lean_dec(x_45);
if (lean_is_scalar(x_42)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_42;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
block_83:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_mk_string_unchecked("subDir", 6, 6);
x_65 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_64);
lean_dec(x_64);
lean_dec(x_41);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
lean_dec(x_43);
lean_dec(x_42);
x_66 = lean_box(0);
x_12 = x_56;
x_13 = x_57;
x_14 = x_63;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_62;
x_19 = x_61;
x_20 = x_66;
goto block_22;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_65, 0);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
lean_free_object(x_65);
lean_dec(x_43);
lean_dec(x_42);
x_69 = lean_box(0);
x_12 = x_56;
x_13 = x_57;
x_14 = x_63;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_62;
x_19 = x_61;
x_20 = x_69;
goto block_22;
}
else
{
lean_object* x_70; 
x_70 = l_Lean_Json_getStr_x3f(x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_free_object(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_mk_string_unchecked("subDir: ", 8, 8);
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
x_44 = x_57;
x_45 = x_73;
goto block_55;
}
else
{
lean_object* x_74; 
lean_dec(x_43);
lean_dec(x_42);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
lean_ctor_set(x_65, 0, x_74);
x_12 = x_56;
x_13 = x_57;
x_14 = x_63;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_62;
x_19 = x_61;
x_20 = x_65;
goto block_22;
}
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec(x_65);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_43);
lean_dec(x_42);
x_76 = lean_box(0);
x_12 = x_56;
x_13 = x_57;
x_14 = x_63;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_62;
x_19 = x_61;
x_20 = x_76;
goto block_22;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_Json_getStr_x3f(x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_mk_string_unchecked("subDir: ", 8, 8);
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_44 = x_57;
x_45 = x_80;
goto block_55;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_43);
lean_dec(x_42);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_12 = x_56;
x_13 = x_57;
x_14 = x_63;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_62;
x_19 = x_61;
x_20 = x_82;
goto block_22;
}
}
}
}
}
block_148:
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_mk_string_unchecked("path", 4, 4);
x_91 = lean_string_dec_eq(x_85, x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_mk_string_unchecked("git", 3, 3);
x_93 = lean_string_dec_eq(x_85, x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_94 = lean_mk_string_unchecked("unknown package entry type '", 28, 28);
x_95 = lean_string_append(x_94, x_85);
lean_dec(x_85);
x_96 = lean_mk_string_unchecked("'", 1, 1);
x_97 = lean_string_append(x_95, x_96);
lean_dec(x_96);
x_44 = x_86;
x_45 = x_97;
goto block_55;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_85);
x_98 = lean_mk_string_unchecked("url", 3, 3);
x_99 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_98);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_100 = lean_mk_string_unchecked("property not found: url", 23, 23);
x_44 = x_86;
x_45 = x_100;
goto block_55;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Json_getStr_x3f(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_mk_string_unchecked("url: ", 5, 5);
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
x_44 = x_86;
x_45 = x_105;
goto block_55;
}
else
{
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_106; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_106 = lean_ctor_get(x_102, 0);
lean_inc(x_106);
lean_dec(x_102);
x_44 = x_86;
x_45 = x_106;
goto block_55;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
lean_dec(x_102);
x_108 = lean_mk_string_unchecked("rev", 3, 3);
x_109 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_108);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_dec(x_107);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_110 = lean_mk_string_unchecked("property not found: rev", 23, 23);
x_44 = x_86;
x_45 = x_110;
goto block_55;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Lean_Json_getStr_x3f(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_mk_string_unchecked("rev: ", 5, 5);
x_115 = lean_string_append(x_114, x_113);
lean_dec(x_113);
x_44 = x_86;
x_45 = x_115;
goto block_55;
}
else
{
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_116; 
lean_dec(x_107);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
lean_dec(x_112);
x_44 = x_86;
x_45 = x_116;
goto block_55;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_mk_string_unchecked("inputRev", 8, 8);
x_119 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_118);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_box(0);
x_56 = x_84;
x_57 = x_86;
x_58 = x_89;
x_59 = x_87;
x_60 = x_117;
x_61 = x_107;
x_62 = x_88;
x_63 = x_120;
goto block_83;
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_119, 0);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
lean_free_object(x_119);
x_123 = lean_box(0);
x_56 = x_84;
x_57 = x_86;
x_58 = x_89;
x_59 = x_87;
x_60 = x_117;
x_61 = x_107;
x_62 = x_88;
x_63 = x_123;
goto block_83;
}
else
{
lean_object* x_124; 
x_124 = l_Lean_Json_getStr_x3f(x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_free_object(x_119);
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_mk_string_unchecked("inputRev: ", 10, 10);
x_127 = lean_string_append(x_126, x_125);
lean_dec(x_125);
x_44 = x_86;
x_45 = x_127;
goto block_55;
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_124, 0);
lean_inc(x_128);
lean_dec(x_124);
lean_ctor_set(x_119, 0, x_128);
x_56 = x_84;
x_57 = x_86;
x_58 = x_89;
x_59 = x_87;
x_60 = x_117;
x_61 = x_107;
x_62 = x_88;
x_63 = x_119;
goto block_83;
}
}
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_119, 0);
lean_inc(x_129);
lean_dec(x_119);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_box(0);
x_56 = x_84;
x_57 = x_86;
x_58 = x_89;
x_59 = x_87;
x_60 = x_117;
x_61 = x_107;
x_62 = x_88;
x_63 = x_130;
goto block_83;
}
else
{
lean_object* x_131; 
x_131 = l_Lean_Json_getStr_x3f(x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_41);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_mk_string_unchecked("inputRev: ", 10, 10);
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_44 = x_86;
x_45 = x_134;
goto block_55;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_56 = x_84;
x_57 = x_86;
x_58 = x_89;
x_59 = x_87;
x_60 = x_117;
x_61 = x_107;
x_62 = x_88;
x_63 = x_136;
goto block_83;
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_85);
x_137 = lean_mk_string_unchecked("dir", 3, 3);
x_138 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_137);
lean_dec(x_137);
lean_dec(x_41);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
x_139 = lean_mk_string_unchecked("property not found: dir", 23, 23);
x_44 = x_86;
x_45 = x_139;
goto block_55;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_Json_getStr_x3f(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec(x_141);
x_143 = lean_mk_string_unchecked("dir: ", 5, 5);
x_144 = lean_string_append(x_143, x_142);
lean_dec(x_142);
x_44 = x_86;
x_45 = x_144;
goto block_55;
}
else
{
uint8_t x_145; 
lean_dec(x_43);
lean_dec(x_42);
x_145 = !lean_is_exclusive(x_141);
if (x_145 == 0)
{
lean_ctor_set_tag(x_141, 0);
x_2 = x_84;
x_3 = x_86;
x_4 = x_89;
x_5 = x_87;
x_6 = x_88;
x_7 = x_141;
goto block_11;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_2 = x_84;
x_3 = x_86;
x_4 = x_89;
x_5 = x_87;
x_6 = x_88;
x_7 = x_147;
goto block_11;
}
}
}
}
}
block_155:
{
lean_object* x_154; 
x_154 = l_Lake_defaultManifestFile;
x_84 = x_149;
x_85 = x_150;
x_86 = x_151;
x_87 = x_152;
x_88 = x_153;
x_89 = x_154;
goto block_148;
}
block_169:
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_mk_string_unchecked("manifestFile", 12, 12);
x_162 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_161);
lean_dec(x_161);
if (lean_obj_tag(x_162) == 0)
{
x_149 = x_156;
x_150 = x_157;
x_151 = x_158;
x_152 = x_159;
x_153 = x_160;
goto block_155;
}
else
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec(x_162);
if (lean_obj_tag(x_163) == 0)
{
x_149 = x_156;
x_150 = x_157;
x_151 = x_158;
x_152 = x_159;
x_153 = x_160;
goto block_155;
}
else
{
lean_object* x_164; 
x_164 = l_Lean_Json_getStr_x3f(x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_41);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_mk_string_unchecked("manifestFile: ", 14, 14);
x_167 = lean_string_append(x_166, x_165);
lean_dec(x_165);
x_44 = x_158;
x_45 = x_167;
goto block_55;
}
else
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
lean_dec(x_164);
x_84 = x_156;
x_85 = x_157;
x_86 = x_158;
x_87 = x_159;
x_88 = x_160;
x_89 = x_168;
goto block_148;
}
}
}
}
block_175:
{
lean_object* x_174; 
x_174 = l_Lake_defaultConfigFile;
x_156 = x_170;
x_157 = x_171;
x_158 = x_172;
x_159 = x_173;
x_160 = x_174;
goto block_169;
}
block_209:
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_mk_string_unchecked("type", 4, 4);
x_179 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_178);
lean_dec(x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
lean_dec(x_177);
lean_dec(x_41);
x_180 = lean_mk_string_unchecked("property not found: type", 24, 24);
x_44 = x_176;
x_45 = x_180;
goto block_55;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_Json_getStr_x3f(x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_177);
lean_dec(x_41);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_mk_string_unchecked("type: ", 6, 6);
x_185 = lean_string_append(x_184, x_183);
lean_dec(x_183);
x_44 = x_176;
x_45 = x_185;
goto block_55;
}
else
{
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_186; 
lean_dec(x_177);
lean_dec(x_41);
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
lean_dec(x_182);
x_44 = x_176;
x_45 = x_186;
goto block_55;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_182, 0);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_mk_string_unchecked("inherited", 9, 9);
x_189 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_188);
lean_dec(x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
lean_dec(x_187);
lean_dec(x_177);
lean_dec(x_41);
x_190 = lean_mk_string_unchecked("property not found: inherited", 29, 29);
x_44 = x_176;
x_45 = x_190;
goto block_55;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Json_getBool_x3f(x_191);
lean_dec(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_187);
lean_dec(x_177);
lean_dec(x_41);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_mk_string_unchecked("inherited: ", 11, 11);
x_195 = lean_string_append(x_194, x_193);
lean_dec(x_193);
x_44 = x_176;
x_45 = x_195;
goto block_55;
}
else
{
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_196; 
lean_dec(x_187);
lean_dec(x_177);
lean_dec(x_41);
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
lean_dec(x_192);
x_44 = x_176;
x_45 = x_196;
goto block_55;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_mk_string_unchecked("configFile", 10, 10);
x_199 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_198);
lean_dec(x_198);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = lean_unbox(x_197);
lean_dec(x_197);
x_170 = x_200;
x_171 = x_187;
x_172 = x_176;
x_173 = x_177;
goto block_175;
}
else
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
lean_dec(x_199);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
x_202 = lean_unbox(x_197);
lean_dec(x_197);
x_170 = x_202;
x_171 = x_187;
x_172 = x_176;
x_173 = x_177;
goto block_175;
}
else
{
lean_object* x_203; 
x_203 = l_Lean_Json_getStr_x3f(x_201);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_177);
lean_dec(x_41);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_mk_string_unchecked("configFile: ", 12, 12);
x_206 = lean_string_append(x_205, x_204);
lean_dec(x_204);
x_44 = x_176;
x_45 = x_206;
goto block_55;
}
else
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_203, 0);
lean_inc(x_207);
lean_dec(x_203);
x_208 = lean_unbox(x_197);
lean_dec(x_197);
x_156 = x_208;
x_157 = x_187;
x_158 = x_176;
x_159 = x_177;
x_160 = x_207;
goto block_169;
}
}
}
}
}
}
}
}
}
}
block_212:
{
lean_object* x_211; 
x_211 = lean_mk_string_unchecked("", 0, 0);
x_176 = x_210;
x_177 = x_211;
goto block_209;
}
block_227:
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_mk_string_unchecked("scope", 5, 5);
x_215 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_41, x_214);
lean_dec(x_214);
if (lean_obj_tag(x_215) == 0)
{
x_210 = x_213;
goto block_212;
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec(x_215);
if (lean_obj_tag(x_216) == 0)
{
x_210 = x_213;
goto block_212;
}
else
{
lean_object* x_217; 
x_217 = l_Lean_Json_getStr_x3f(x_216);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
lean_dec(x_213);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_mk_string_unchecked("scope: ", 7, 7);
x_221 = lean_string_append(x_220, x_219);
lean_dec(x_219);
lean_ctor_set(x_217, 0, x_221);
return x_217;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
lean_dec(x_217);
x_223 = lean_mk_string_unchecked("scope: ", 7, 7);
x_224 = lean_string_append(x_223, x_222);
lean_dec(x_222);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
return x_225;
}
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_217, 0);
lean_inc(x_226);
lean_dec(x_217);
x_176 = x_213;
x_177 = x_226;
goto block_209;
}
}
}
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_20);
x_2 = x_12;
x_3 = x_13;
x_4 = x_15;
x_5 = x_16;
x_6 = x_18;
x_7 = x_21;
goto block_11;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_mk_string_unchecked("name: ", 6, 6);
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_23 = x_29;
goto block_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_fromJson_x3f___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageEntry_fromJson_x3f___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageEntry_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_PackageEntry_fromJson_x3f), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_box(1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*5, x_9);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setInherited___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageEntry_setInherited(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*5, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setConfigFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageEntry_setConfigFile(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set(x_8, 4, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*5, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_setManifestFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageEntry_setManifestFile(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_inDirectory(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = l_Lake_joinRelative(x_1, x_10);
lean_dec(x_10);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_3);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Lake_joinRelative(x_1, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set(x_16, 3, x_8);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_6);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_3);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = l_Lake_defaultConfigFile;
x_7 = lean_box(0);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_4);
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l_Lake_defaultConfigFile;
x_18 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_19 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_11);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageEntry_ofV6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageEntry_ofV6(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_addPackage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_toJson_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lake_PackageEntry_toJson(x_5);
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
LEAN_EXPORT lean_object* l_Lake_Manifest_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_42; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Load_Manifest_0__Lake_toJsonPackageEntryV6___lam__0____x40_Lake_Load_Manifest___hyg_456____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("version", 7, 7);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = lean_mk_string_unchecked("", 0, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_StdVer_toString(x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("name", 4, 4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Name_toString(x_13, x_15, x_2);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("lakeDir", 7, 7);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l_Lake_mkRelPathString(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("packagesDir", 11, 11);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_25 = x_43;
goto block_41;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = l_Lake_mkRelPathString(x_45);
lean_ctor_set_tag(x_42, 3);
lean_ctor_set(x_42, 0, x_46);
x_25 = x_42;
goto block_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Lake_mkRelPathString(x_47);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_25 = x_49;
goto block_41;
}
}
block_41:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("packages", 8, 8);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_array_size(x_28);
x_30 = lean_usize_of_nat(x_5);
x_31 = l_Array_mapMUnsafe_map___at___Lake_Manifest_toJson_spec__0(x_29, x_30, x_28);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Json_mkObj(x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_toJson_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Manifest_toJson_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Manifest_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Manifest_toJson), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_36; lean_object* x_45; lean_object* x_74; lean_object* x_75; 
x_74 = lean_mk_string_unchecked("version", 7, 7);
x_75 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_1, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_mk_string_unchecked("schemaVersion", 13, 13);
x_77 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_1, x_76);
lean_dec(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_mk_string_unchecked("property not found: schemaVersion", 33, 33);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_45 = x_80;
goto block_73;
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
lean_dec(x_75);
x_45 = x_81;
goto block_73;
}
block_35:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_alloc_closure((void*)(l_Lake_StdVer_compare___boxed), 2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(5u);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_2);
x_13 = l_Ord_instDecidableRelLt___redArg(x_7, x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_15 = lean_mk_string_unchecked("incompatible manifest version '", 31, 31);
x_16 = l_Lake_StdVer_toString(x_2);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_21 = lean_mk_string_unchecked("schema version '", 16, 16);
x_22 = l_Lake_StdVer_toString(x_2);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("' is of a higher major version than this Lake's '", 49, 49);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lake_StdVer_toString(x_29);
x_31 = lean_string_append(x_25, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("'; you may need to update your 'lean-toolchain'", 47, 47);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
block_44:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_mk_string_unchecked("invalid version '", 17, 17);
x_38 = lean_unsigned_to_nat(80u);
x_39 = l_Lean_Json_pretty(x_36, x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = lean_mk_string_unchecked("'; you may need to update your 'lean-toolchain'", 47, 47);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
block_73:
{
switch (lean_obj_tag(x_45)) {
case 2:
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_to_int(x_50);
x_52 = lean_int_dec_lt(x_48, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_53 == 0)
{
lean_free_object(x_46);
lean_dec(x_48);
x_36 = x_45;
goto block_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
x_54 = lean_nat_abs(x_48);
lean_dec(x_48);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_50);
x_56 = lean_mk_string_unchecked("", 0, 0);
lean_ctor_set(x_46, 1, x_56);
lean_ctor_set(x_46, 0, x_55);
x_2 = x_46;
goto block_35;
}
}
else
{
lean_free_object(x_46);
lean_dec(x_49);
lean_dec(x_48);
x_36 = x_45;
goto block_44;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_46, 0);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_46);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_to_int(x_59);
x_61 = lean_int_dec_lt(x_57, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_62 == 0)
{
lean_dec(x_57);
x_36 = x_45;
goto block_44;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_45);
x_63 = lean_nat_abs(x_57);
lean_dec(x_57);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_59);
x_65 = lean_mk_string_unchecked("", 0, 0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_2 = x_66;
goto block_35;
}
}
else
{
lean_dec(x_58);
lean_dec(x_57);
x_36 = x_45;
goto block_44;
}
}
}
case 3:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
lean_dec(x_45);
x_68 = l_Lake_StdVer_parse(x_67);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_2 = x_72;
goto block_35;
}
}
default: 
{
x_36 = x_45;
goto block_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getVersion___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Manifest_getVersion(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lake_PackageEntry_ofV6(x_5);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l_Lake_PackageEntry_fromJson_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = l___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115_(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_7; lean_object* x_12; lean_object* x_22; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_alloc_closure((void*)(l_Lake_StdVer_compare___boxed), 2, 0);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_unsigned_to_nat(7u);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Ord_instDecidableRelLt___redArg(x_27, x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_mk_string_unchecked("packages", 8, 8);
x_35 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_2, x_34);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
goto block_6;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
goto block_6;
}
else
{
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_array_size(x_37);
x_39 = lean_usize_of_nat(x_28);
x_40 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__1(x_38, x_39, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_7 = x_41;
goto block_11;
}
else
{
return x_40;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_43 = lean_unsigned_to_nat(80u);
x_44 = l_Lean_Json_pretty(x_36, x_43);
x_45 = lean_string_append(x_42, x_44);
lean_dec(x_44);
x_46 = lean_mk_string_unchecked("'", 1, 1);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_7 = x_47;
goto block_11;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_mk_string_unchecked("packages", 8, 8);
x_49 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_2, x_48);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
goto block_21;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
goto block_21;
}
else
{
if (lean_obj_tag(x_50) == 4)
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_array_size(x_51);
x_53 = lean_usize_of_nat(x_28);
x_54 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__2(x_52, x_53, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_22 = x_55;
goto block_26;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_12 = x_56;
goto block_18;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_58 = lean_unsigned_to_nat(80u);
x_59 = l_Lean_Json_pretty(x_50, x_58);
x_60 = lean_string_append(x_57, x_59);
lean_dec(x_59);
x_61 = lean_mk_string_unchecked("'", 1, 1);
x_62 = lean_string_append(x_60, x_61);
lean_dec(x_61);
x_22 = x_62;
goto block_26;
}
}
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_mk_string_unchecked("packages: ", 10, 10);
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_18:
{
size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
x_16 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(x_13, x_15, x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_12 = x_20;
goto block_18;
}
block_26:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_mk_string_unchecked("packages: ", 10, 10);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Manifest_getPackages_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_getPackages___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Manifest_getPackages(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_7; 
x_7 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lake_Manifest_getVersion(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_33; lean_object* x_34; lean_object* x_62; lean_object* x_65; lean_object* x_82; lean_object* x_83; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_82 = lean_mk_string_unchecked("name", 4, 4);
x_83 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_11, x_82);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
goto block_81;
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
goto block_81;
}
else
{
lean_object* x_85; 
lean_inc(x_84);
x_85 = l_Lean_Json_getStr_x3f(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
lean_dec(x_84);
lean_dec(x_16);
lean_dec(x_11);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
x_2 = x_86;
goto block_6;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_89 = lean_string_dec_eq(x_87, x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_String_toName(x_87);
x_91 = l_Lean_Name_isAnonymous(x_90);
if (x_91 == 0)
{
lean_dec(x_84);
x_65 = x_90;
goto block_79;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_11);
x_92 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_93 = lean_unsigned_to_nat(80u);
x_94 = l_Lean_Json_pretty(x_84, x_93);
x_95 = lean_string_append(x_92, x_94);
lean_dec(x_94);
x_96 = lean_mk_string_unchecked("'", 1, 1);
x_97 = lean_string_append(x_95, x_96);
lean_dec(x_96);
x_2 = x_97;
goto block_6;
}
}
else
{
lean_object* x_98; 
lean_dec(x_87);
lean_dec(x_84);
x_98 = lean_box(0);
x_65 = x_98;
goto block_79;
}
}
}
}
block_32:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lake_Manifest_getPackages(x_21, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
block_61:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_mk_string_unchecked("packagesDir", 11, 11);
x_36 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_11, x_35);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_17 = x_33;
x_18 = x_34;
x_19 = x_37;
goto block_32;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_36, 0);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_free_object(x_36);
x_40 = lean_box(0);
x_17 = x_33;
x_18 = x_34;
x_19 = x_40;
goto block_32;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Json_getStr_x3f(x_39);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_free_object(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_16);
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_mk_string_unchecked("packagesDir: ", 13, 13);
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_mk_string_unchecked("packagesDir: ", 13, 13);
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec(x_41);
lean_ctor_set(x_36, 0, x_50);
x_17 = x_33;
x_18 = x_34;
x_19 = x_36;
goto block_32;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_36, 0);
lean_inc(x_51);
lean_dec(x_36);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_17 = x_33;
x_18 = x_34;
x_19 = x_52;
goto block_32;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_Json_getStr_x3f(x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_16);
lean_dec(x_11);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_mk_string_unchecked("packagesDir: ", 13, 13);
x_57 = lean_string_append(x_56, x_54);
lean_dec(x_54);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_17 = x_33;
x_18 = x_34;
x_19 = x_60;
goto block_32;
}
}
}
}
}
block_64:
{
lean_object* x_63; 
x_63 = l_Lake_defaultLakeDir;
x_33 = x_62;
x_34 = x_63;
goto block_61;
}
block_79:
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_mk_string_unchecked("lakeDir", 7, 7);
x_67 = l_Lean_RBNode_find___at_____private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___redArg(x_11, x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
x_62 = x_65;
goto block_64;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
x_62 = x_65;
goto block_64;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_Json_getStr_x3f(x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_65);
lean_dec(x_16);
lean_dec(x_11);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_mk_string_unchecked("lakeDir: ", 9, 9);
x_73 = lean_string_append(x_72, x_71);
lean_dec(x_71);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_mk_string_unchecked("lakeDir: ", 9, 9);
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
lean_dec(x_69);
x_33 = x_65;
x_34 = x_78;
goto block_61;
}
}
}
}
block_81:
{
lean_object* x_80; 
x_80 = lean_box(0);
x_65 = x_80;
goto block_79;
}
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("name: ", 6, 6);
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lake_Manifest_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Manifest_fromJson_x3f), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lake_Manifest_fromJson_x3f(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
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
x_14 = l_Lean_Json_parse(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lake_Manifest_fromJson_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_7 = x_20;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked(": ", 2, 2);
x_9 = lean_string_append(x_1, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_6;
 lean_ctor_set_tag(x_12, 1);
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_load_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
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
x_14 = l_Lean_Json_parse(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lake_Manifest_fromJson_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_7 = x_20;
goto block_13;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked(": ", 2, 2);
x_9 = lean_string_append(x_1, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_6;
 lean_ctor_set_tag(x_12, 1);
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 11)
{
uint8_t x_27; 
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_3, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
return x_3;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lake_Manifest_toJson(x_1);
x_5 = lean_unsigned_to_nat(80u);
x_6 = l_Lean_Json_pretty(x_4, x_5);
x_7 = lean_unsigned_to_nat(10u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_string_push(x_6, x_8);
x_10 = l_IO_FS_writeFile(x_2, x_9, x_3);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_save___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_save(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_save(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveToFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_saveToFile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_decodeEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lake_Manifest_getVersion(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_Manifest_getPackages(x_13, x_6);
lean_dec(x_6);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_parseEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lake_Manifest_decodeEntries(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_loadEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
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
x_14 = l_Lean_Json_parse(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_7 = x_17;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lake_Manifest_decodeEntries(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_7 = x_20;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked(": ", 2, 2);
x_9 = lean_string_append(x_1, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_7);
lean_dec(x_7);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(1, 2, 0);
} else {
 x_12 = x_6;
 lean_ctor_set_tag(x_12, 1);
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_tryLoadEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_12; 
x_12 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_22 = l_Lean_Json_parse(x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_16 = x_25;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lake_Manifest_decodeEntries(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_free_object(x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_16 = x_28;
goto block_21;
}
else
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_12, 0, x_29);
return x_12;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_mk_string_unchecked(": ", 2, 2);
lean_inc(x_1);
x_18 = lean_string_append(x_1, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_16);
lean_dec(x_16);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_3 = x_20;
x_4 = x_15;
goto block_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_38 = l_Lean_Json_parse(x_30);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_mk_string_unchecked("invalid JSON: ", 14, 14);
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_32 = x_41;
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lake_Manifest_decodeEntries(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_32 = x_44;
goto block_37;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_31);
return x_46;
}
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_mk_string_unchecked(": ", 2, 2);
lean_inc(x_1);
x_34 = lean_string_append(x_1, x_33);
lean_dec(x_33);
x_35 = lean_string_append(x_34, x_32);
lean_dec(x_32);
x_36 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_3 = x_36;
x_4 = x_31;
goto block_11;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_12, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 11)
{
uint8_t x_48; 
lean_dec(x_47);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_12, 0);
lean_dec(x_49);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_mk_empty_array_with_capacity(x_50);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_51);
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_mk_empty_array_with_capacity(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_dec(x_12);
x_3 = x_47;
x_4 = x_56;
goto block_11;
}
}
block_11:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_mk_string_unchecked(": ", 2, 2);
x_6 = lean_string_append(x_1, x_5);
lean_dec(x_5);
x_7 = lean_io_error_to_string(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; lean_object* x_28; 
x_4 = lean_mk_string_unchecked("schemaVersion", 13, 13);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lake_StdVer_toString(x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("packages", 8, 8);
x_14 = lean_array_size(x_2);
x_15 = lean_usize_of_nat(x_6);
x_16 = l_Array_mapMUnsafe_map___at___Lake_Manifest_toJson_spec__0(x_14, x_15, x_2);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Json_mkObj(x_21);
x_23 = lean_unsigned_to_nat(80u);
x_24 = l_Lean_Json_pretty(x_22, x_23);
x_25 = lean_unsigned_to_nat(10u);
x_26 = l_Char_ofNat(x_25);
x_27 = lean_string_push(x_24, x_26);
x_28 = l_IO_FS_writeFile(x_1, x_27, x_3);
lean_dec(x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lake_Manifest_saveEntries___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Manifest_saveEntries(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Version(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Manifest(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_JsonObject(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Manifest_version = _init_l_Lake_Manifest_version();
lean_mark_persistent(l_Lake_Manifest_version);
l_Lake_instFromJsonPackageEntryV6 = _init_l_Lake_instFromJsonPackageEntryV6();
lean_mark_persistent(l_Lake_instFromJsonPackageEntryV6);
l_Lake_instToJsonPackageEntryV6 = _init_l_Lake_instToJsonPackageEntryV6();
lean_mark_persistent(l_Lake_instToJsonPackageEntryV6);
l_Lake_instInhabitedPackageEntryV6 = _init_l_Lake_instInhabitedPackageEntryV6();
lean_mark_persistent(l_Lake_instInhabitedPackageEntryV6);
l_Lake_instInhabitedPackageEntrySrc = _init_l_Lake_instInhabitedPackageEntrySrc();
lean_mark_persistent(l_Lake_instInhabitedPackageEntrySrc);
l_Lake_instInhabitedPackageEntry = _init_l_Lake_instInhabitedPackageEntry();
lean_mark_persistent(l_Lake_instInhabitedPackageEntry);
l_Lake_PackageEntry_instToJson = _init_l_Lake_PackageEntry_instToJson();
lean_mark_persistent(l_Lake_PackageEntry_instToJson);
l_Lake_PackageEntry_instFromJson = _init_l_Lake_PackageEntry_instFromJson();
lean_mark_persistent(l_Lake_PackageEntry_instFromJson);
l_Lake_Manifest_instToJson = _init_l_Lake_Manifest_instToJson();
lean_mark_persistent(l_Lake_Manifest_instToJson);
l_Lake_Manifest_instFromJson = _init_l_Lake_Manifest_instFromJson();
lean_mark_persistent(l_Lake_Manifest_instFromJson);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
