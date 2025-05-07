// Lean compiler output
// Module: Lean.Data.Lsp.Client
// Imports: Lean.Data.Lsp.Basic Lean.Data.Json
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_34_(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRegistrationParams;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRegistration;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistration;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296_(lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258_(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistrationParams;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_1063__spec__0(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_34_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("id", 2, 2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("method", 6, 6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_mk_string_unchecked("registerOptions", 15, 15);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_dec(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_14 = x_27;
goto block_25;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_14 = x_28;
goto block_25;
}
block_25:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_20, x_22);
x_24 = l_Lean_Json_mkObj(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRegistration() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_34_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("id", 2, 2);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_1063__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("Registration", 12, 12);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("Registration", 12, 12);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_mk_string_unchecked("method", 6, 6);
lean_inc(x_1);
x_47 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_1063__spec__0(x_1, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Lsp", 3, 3);
x_53 = lean_mk_string_unchecked("Registration", 12, 12);
x_54 = l_Lean_Name_mkStr3(x_51, x_52, x_53);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_50);
x_57 = l_Lean_Name_toString(x_54, x_56, x_50);
x_58 = lean_mk_string_unchecked(".", 1, 1);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_Name_mkStr1(x_46);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_50);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(": ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_49);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_66);
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Lsp", 3, 3);
x_71 = lean_mk_string_unchecked("Registration", 12, 12);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
lean_inc(x_68);
x_75 = l_Lean_Name_toString(x_72, x_74, x_68);
x_76 = lean_mk_string_unchecked(".", 1, 1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = l_Lean_Name_mkStr1(x_46);
x_79 = lean_unbox(x_73);
x_80 = l_Lean_Name_toString(x_78, x_79, x_68);
x_81 = lean_string_append(x_77, x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked(": ", 2, 2);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_string_append(x_83, x_67);
lean_dec(x_67);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_86; 
lean_dec(x_45);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
lean_ctor_set_tag(x_47, 0);
return x_47;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_47, 0);
lean_inc(x_89);
lean_dec(x_47);
x_90 = lean_mk_string_unchecked("registerOptions", 15, 15);
x_91 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100__spec__0(x_1, x_90);
lean_dec(x_90);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_45);
lean_ctor_set(x_94, 1, x_89);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 0);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_45);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set(x_96, 2, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_34_(x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258_(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("registrations", 13, 13);
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258__spec__0(x_3, x_5, x_1);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_empty_array_with_capacity(x_4);
x_14 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_221__spec__0(x_12, x_13);
x_15 = l_Lean_Json_mkObj(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258__spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonRegistrationParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_258_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration____x40_Lean_Data_Lsp_Client___hyg_100_(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0_spec__0(x_5, x_7, x_4);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("registrations", 13, 13);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("RegistrationParams", 18, 18);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistration___lam__0____x40_Lean_Data_Lsp_Client___hyg_100____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("RegistrationParams", 18, 18);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_fromJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_296_), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Client(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instToJsonRegistration = _init_l_Lean_Lsp_instToJsonRegistration();
lean_mark_persistent(l_Lean_Lsp_instToJsonRegistration);
l_Lean_Lsp_instFromJsonRegistration = _init_l_Lean_Lsp_instFromJsonRegistration();
lean_mark_persistent(l_Lean_Lsp_instFromJsonRegistration);
l_Lean_Lsp_instToJsonRegistrationParams = _init_l_Lean_Lsp_instToJsonRegistrationParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonRegistrationParams);
l_Lean_Lsp_instFromJsonRegistrationParams = _init_l_Lean_Lsp_instFromJsonRegistrationParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonRegistrationParams);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
