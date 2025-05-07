// Lean compiler output
// Module: Lean.Util.Paths
// Imports: Lean.Data.Json Lean.Util.Path
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonLeanPaths;
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135_(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonLeanPaths;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0_spec__0(size_t, size_t, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = lean_array_uget(x_3, x_2);
lean_dec(x_3);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_6, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_2 = lean_mk_string_unchecked("oleanPath", 9, 9);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_array_mk(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(x_5, x_7, x_4);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("srcPath", 7, 7);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_array_mk(x_14);
x_16 = lean_array_size(x_15);
x_17 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(x_16, x_7, x_15);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
x_21 = lean_mk_string_unchecked("loadDynlibPaths", 15, 15);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_array_size(x_22);
x_24 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(x_23, x_7, x_22);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
x_28 = lean_mk_string_unchecked("pluginPaths", 11, 11);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_array_size(x_29);
x_31 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(x_30, x_7, x_29);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_20);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_empty_array_with_capacity(x_6);
x_41 = l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(x_39, x_40);
x_42 = l_Lean_Json_mkObj(x_41);
return x_42;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonLeanPaths() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_getStr_x3f(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0_spec__0(x_5, x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_to_list(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_to_list(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_19 = lean_unsigned_to_nat(80u);
x_20 = l_Lean_Json_pretty(x_3, x_19);
x_21 = lean_string_append(x_18, x_20);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; size_t x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0_spec__0(x_5, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_mk_string_unchecked("expected JSON array, got '", 26, 26);
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_3, x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("oleanPath", 9, 9);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("LeanPaths", 9, 9);
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
x_23 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("LeanPaths", 9, 9);
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
x_44 = lean_mk_string_unchecked("srcPath", 7, 7);
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_43);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("LeanPaths", 9, 9);
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
x_65 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_66 = lean_mk_string_unchecked("Lean", 4, 4);
x_67 = lean_mk_string_unchecked("LeanPaths", 9, 9);
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
lean_dec(x_1);
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
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_45, 0);
lean_inc(x_85);
lean_dec(x_45);
x_86 = lean_mk_string_unchecked("loadDynlibPaths", 15, 15);
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("LeanPaths", 9, 9);
x_93 = l_Lean_Name_mkStr2(x_91, x_92);
x_94 = lean_box(1);
x_95 = lean_unbox(x_94);
lean_inc(x_90);
x_96 = l_Lean_Name_toString(x_93, x_95, x_90);
x_97 = lean_mk_string_unchecked(".", 1, 1);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
x_99 = l_Lean_Name_mkStr1(x_86);
x_100 = lean_unbox(x_94);
x_101 = l_Lean_Name_toString(x_99, x_100, x_90);
x_102 = lean_string_append(x_98, x_101);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked(": ", 2, 2);
x_104 = lean_string_append(x_102, x_103);
lean_dec(x_103);
x_105 = lean_string_append(x_104, x_89);
lean_dec(x_89);
lean_ctor_set(x_87, 0, x_105);
return x_87;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec(x_87);
x_107 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_108 = lean_mk_string_unchecked("Lean", 4, 4);
x_109 = lean_mk_string_unchecked("LeanPaths", 9, 9);
x_110 = l_Lean_Name_mkStr2(x_108, x_109);
x_111 = lean_box(1);
x_112 = lean_unbox(x_111);
lean_inc(x_107);
x_113 = l_Lean_Name_toString(x_110, x_112, x_107);
x_114 = lean_mk_string_unchecked(".", 1, 1);
x_115 = lean_string_append(x_113, x_114);
lean_dec(x_114);
x_116 = l_Lean_Name_mkStr1(x_86);
x_117 = lean_unbox(x_111);
x_118 = l_Lean_Name_toString(x_116, x_117, x_107);
x_119 = lean_string_append(x_115, x_118);
lean_dec(x_118);
x_120 = lean_mk_string_unchecked(": ", 2, 2);
x_121 = lean_string_append(x_119, x_120);
lean_dec(x_120);
x_122 = lean_string_append(x_121, x_106);
lean_dec(x_106);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_124; 
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_87);
if (x_124 == 0)
{
lean_ctor_set_tag(x_87, 0);
return x_87;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_87, 0);
lean_inc(x_125);
lean_dec(x_87);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_87, 0);
lean_inc(x_127);
lean_dec(x_87);
x_128 = lean_mk_string_unchecked("pluginPaths", 11, 11);
x_129 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_133 = lean_mk_string_unchecked("Lean", 4, 4);
x_134 = lean_mk_string_unchecked("LeanPaths", 9, 9);
x_135 = l_Lean_Name_mkStr2(x_133, x_134);
x_136 = lean_box(1);
x_137 = lean_unbox(x_136);
lean_inc(x_132);
x_138 = l_Lean_Name_toString(x_135, x_137, x_132);
x_139 = lean_mk_string_unchecked(".", 1, 1);
x_140 = lean_string_append(x_138, x_139);
lean_dec(x_139);
x_141 = l_Lean_Name_mkStr1(x_128);
x_142 = lean_unbox(x_136);
x_143 = l_Lean_Name_toString(x_141, x_142, x_132);
x_144 = lean_string_append(x_140, x_143);
lean_dec(x_143);
x_145 = lean_mk_string_unchecked(": ", 2, 2);
x_146 = lean_string_append(x_144, x_145);
lean_dec(x_145);
x_147 = lean_string_append(x_146, x_131);
lean_dec(x_131);
lean_ctor_set(x_129, 0, x_147);
return x_129;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec(x_129);
x_149 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed), 1, 0);
x_150 = lean_mk_string_unchecked("Lean", 4, 4);
x_151 = lean_mk_string_unchecked("LeanPaths", 9, 9);
x_152 = l_Lean_Name_mkStr2(x_150, x_151);
x_153 = lean_box(1);
x_154 = lean_unbox(x_153);
lean_inc(x_149);
x_155 = l_Lean_Name_toString(x_152, x_154, x_149);
x_156 = lean_mk_string_unchecked(".", 1, 1);
x_157 = lean_string_append(x_155, x_156);
lean_dec(x_156);
x_158 = l_Lean_Name_mkStr1(x_128);
x_159 = lean_unbox(x_153);
x_160 = l_Lean_Name_toString(x_158, x_159, x_149);
x_161 = lean_string_append(x_157, x_160);
lean_dec(x_160);
x_162 = lean_mk_string_unchecked(": ", 2, 2);
x_163 = lean_string_append(x_161, x_162);
lean_dec(x_162);
x_164 = lean_string_append(x_163, x_148);
lean_dec(x_148);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
else
{
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_166; 
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_166 = !lean_is_exclusive(x_129);
if (x_166 == 0)
{
lean_ctor_set_tag(x_129, 0);
return x_129;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_129, 0);
lean_inc(x_167);
lean_dec(x_129);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_129);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_129, 0);
x_171 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_171, 0, x_43);
lean_ctor_set(x_171, 1, x_85);
lean_ctor_set(x_171, 2, x_127);
lean_ctor_set(x_171, 3, x_170);
lean_ctor_set(x_129, 0, x_171);
return x_129;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_129, 0);
lean_inc(x_172);
lean_dec(x_129);
x_173 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_173, 0, x_43);
lean_ctor_set(x_173, 1, x_85);
lean_ctor_set(x_173, 2, x_127);
lean_ctor_set(x_173, 3, x_172);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
return x_174;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths___lam__0____x40_Lean_Util_Paths___hyg_135_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonLeanPaths() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135_), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToJsonLeanPaths = _init_l_Lean_instToJsonLeanPaths();
lean_mark_persistent(l_Lean_instToJsonLeanPaths);
l_Lean_instFromJsonLeanPaths = _init_l_Lean_instFromJsonLeanPaths();
lean_mark_persistent(l_Lean_instFromJsonLeanPaths);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
