// Lean compiler output
// Module: Lean.Setup
// Imports: Lean.Data.Json Lean.Util.LeanOptions
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprImport____x40_Lean_Setup___hyg_34_(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleArtifacts___redArg____x40_Lean_Setup___hyg_417_(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport___lam__0(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprImport____x40_Lean_Setup___hyg_34____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleSetup;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___redArg___lam__0(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprImport___redArg____x40_Lean_Setup___hyg_34_(lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549_(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonModuleArtifacts;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprModuleSetup;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport;
LEAN_EXPORT lean_object* l_Lean_instToStringImport;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringImport___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedModuleSetup;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549__spec__0(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonImport____x40_Lean_Setup___hyg_124_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedModuleArtifacts;
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedImport;
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg____x40_Lean_Setup___hyg_913_(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209_(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__1____x40_Lean_Setup___hyg_913____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__1____x40_Lean_Setup___hyg_913_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprImport;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions___redArg____x40_Lean_Util_LeanOptions___hyg_541_(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleArtifacts;
LEAN_EXPORT lean_object* l_Lean_instReprModuleArtifacts;
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__0____x40_Lean_Setup___hyg_913_(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417_(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonModuleSetup;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFromJsonImport;
LEAN_EXPORT lean_object* l_Lean_instToJsonImport;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprImport___redArg____x40_Lean_Setup___hyg_34_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_68; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("module", 6, 6);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(10u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Name_reprPrec(x_12, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_15);
x_36 = lean_unbox(x_16);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_mk_string_unchecked(",", 1, 1);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_inc(x_39);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("importAll", 9, 9);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_8);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_8);
x_47 = lean_unsigned_to_nat(13u);
x_48 = lean_nat_to_int(x_47);
x_68 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_mk_string_unchecked("false", 5, 5);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_49 = x_70;
goto block_67;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_mk_string_unchecked("true", 4, 4);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_49 = x_72;
goto block_67;
}
block_34:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unbox(x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_mk_string_unchecked(" }", 2, 2);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unbox(x_16);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
return x_32;
}
block_67:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_unbox(x_16);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_52);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_39);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_41);
x_56 = lean_mk_string_unchecked("isExported", 10, 10);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_8);
x_60 = lean_unsigned_to_nat(14u);
x_61 = lean_nat_to_int(x_60);
x_62 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_mk_string_unchecked("false", 5, 5);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_17 = x_59;
x_18 = x_61;
x_19 = x_64;
goto block_34;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_mk_string_unchecked("true", 4, 4);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_17 = x_59;
x_18 = x_61;
x_19 = x_66;
goto block_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprImport____x40_Lean_Setup___hyg_34_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Setup_0__Lean_reprImport___redArg____x40_Lean_Setup___hyg_34_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprImport____x40_Lean_Setup___hyg_34____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Setup_0__Lean_reprImport____x40_Lean_Setup___hyg_34_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprImport() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_reprImport____x40_Lean_Setup___hyg_34____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedImport() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_5);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonImport____x40_Lean_Setup___hyg_124_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("module", 6, 6);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Name_toString(x_4, x_6, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("importAll", 9, 9);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_14 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_mk_string_unchecked("isExported", 10, 10);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_26);
x_28 = l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(x_25, x_27);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToJsonImport() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport____x40_Lean_Setup___hyg_124_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
lean_inc(x_3);
x_4 = l_Lean_Json_getStr_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_String_toName(x_9);
x_13 = l_Lean_Name_isAnonymous(x_12);
if (x_13 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_15 = lean_unsigned_to_nat(80u);
x_16 = l_Lean_Json_pretty(x_3, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
}
else
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_3);
x_20 = lean_box(0);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_23 = lean_string_dec_eq(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_String_toName(x_21);
x_25 = l_Lean_Name_isAnonymous(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_27 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_28 = lean_unsigned_to_nat(80u);
x_29 = l_Lean_Json_pretty(x_3, x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("'", 1, 1);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getBool_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("module", 6, 6);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Import", 6, 6);
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
x_23 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("Import", 6, 6);
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
x_44 = lean_mk_string_unchecked("importAll", 9, 9);
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(x_1, x_44);
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
x_48 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Import", 6, 6);
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
x_65 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_66 = lean_mk_string_unchecked("Lean", 4, 4);
x_67 = lean_mk_string_unchecked("Import", 6, 6);
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
x_86 = lean_mk_string_unchecked("isExported", 10, 10);
x_87 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
lean_dec(x_85);
lean_dec(x_43);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("Import", 6, 6);
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
x_107 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_108 = lean_mk_string_unchecked("Lean", 4, 4);
x_109 = lean_mk_string_unchecked("Import", 6, 6);
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
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_87);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_87, 0);
x_129 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_129, 0, x_43);
x_130 = lean_unbox(x_85);
lean_dec(x_85);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_130);
x_131 = lean_unbox(x_128);
lean_dec(x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*1 + 1, x_131);
lean_ctor_set(x_87, 0, x_129);
return x_87;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_87, 0);
lean_inc(x_132);
lean_dec(x_87);
x_133 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_133, 0, x_43);
x_134 = lean_unbox(x_85);
lean_dec(x_85);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_134);
x_135 = lean_unbox(x_132);
lean_dec(x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*1 + 1, x_135);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_133);
return x_136;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonImport() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeNameImport___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_5);
x_6 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_6);
return x_4;
}
}
static lean_object* _init_l_Lean_instCoeNameImport() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instCoeNameImport___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringImport___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Name_toString(x_3, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_instToStringImport() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_instToStringImport___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("none", 4, 4);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_mk_string_unchecked("some ", 5, 5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_7);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_String_quote(x_6);
lean_dec(x_6);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Repr_addAppParen(x_13, x_8);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_mk_string_unchecked("some ", 5, 5);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(1024u);
x_21 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_String_quote(x_17);
lean_dec(x_17);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Repr_addAppParen(x_25, x_20);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Repr_addAppParen(x_27, x_2);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleArtifacts___redArg____x40_Lean_Setup___hyg_417_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("lean\?", 5, 5);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(9u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(x_12, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_mk_string_unchecked(",", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("olean\?", 6, 6);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(10u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(x_31, x_13);
lean_inc(x_30);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_21);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
x_39 = lean_mk_string_unchecked("oleanServer\?", 12, 12);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_8);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(x_45, x_13);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unbox(x_16);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_48);
lean_inc(x_21);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_21);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_23);
x_53 = lean_mk_string_unchecked("oleanPrivate\?", 13, 13);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_8);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_8);
x_57 = lean_unsigned_to_nat(17u);
x_58 = lean_nat_to_int(x_57);
x_59 = lean_ctor_get(x_1, 3);
lean_inc(x_59);
x_60 = l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(x_59, x_13);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox(x_16);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_21);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_23);
x_67 = lean_mk_string_unchecked("ilean\?", 6, 6);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
x_71 = lean_ctor_get(x_1, 4);
lean_inc(x_71);
lean_dec(x_1);
x_72 = l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(x_71, x_13);
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_30);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_unbox(x_16);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_75);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_mk_string_unchecked(" }", 2, 2);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_to_int(x_78);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_2);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_unbox(x_16);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_86);
return x_85;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Setup_0__Lean_reprModuleArtifacts___redArg____x40_Lean_Setup___hyg_417_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at_____private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprModuleArtifacts() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_reprModuleArtifacts____x40_Lean_Setup___hyg_417____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedModuleArtifacts() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_ctor_set_tag(x_2, 3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("lean", 4, 4);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_Json_opt___at_____private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549__spec__0(x_2, x_3);
x_5 = lean_mk_string_unchecked("olean", 5, 5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Json_opt___at_____private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549__spec__0(x_5, x_6);
x_8 = lean_mk_string_unchecked("oleanServer", 11, 11);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = l_Lean_Json_opt___at_____private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549__spec__0(x_8, x_9);
x_11 = lean_mk_string_unchecked("oleanPrivate", 12, 12);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = l_Lean_Json_opt___at_____private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549__spec__0(x_11, x_12);
x_14 = lean_mk_string_unchecked("ilean", 5, 5);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Json_opt___at_____private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549__spec__0(x_14, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(x_22, x_24);
x_26 = l_Lean_Json_mkObj(x_25);
return x_26;
}
}
static lean_object* _init_l_Lean_instToJsonModuleArtifacts() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; 
x_6 = l_Lean_Json_getStr_x3f(x_3);
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("lean", 4, 4);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc(x_6);
x_12 = l_Lean_Name_toString(x_9, x_11, x_6);
x_13 = lean_mk_string_unchecked(".", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("lean\?", 5, 5);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unbox(x_10);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_14, x_18);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
lean_inc(x_24);
x_30 = l_Lean_Name_toString(x_27, x_29, x_24);
x_31 = lean_mk_string_unchecked(".", 1, 1);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("lean\?", 5, 5);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_unbox(x_28);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_32, x_36);
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
x_46 = lean_mk_string_unchecked("olean", 5, 5);
lean_inc(x_1);
x_47 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(x_1, x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_53 = l_Lean_Name_mkStr2(x_51, x_52);
x_54 = lean_box(1);
x_55 = lean_unbox(x_54);
lean_inc(x_50);
x_56 = l_Lean_Name_toString(x_53, x_55, x_50);
x_57 = lean_mk_string_unchecked(".", 1, 1);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = lean_mk_string_unchecked("olean\?", 6, 6);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = lean_unbox(x_54);
x_62 = l_Lean_Name_toString(x_60, x_61, x_50);
x_63 = lean_string_append(x_58, x_62);
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
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_71 = l_Lean_Name_mkStr2(x_69, x_70);
x_72 = lean_box(1);
x_73 = lean_unbox(x_72);
lean_inc(x_68);
x_74 = l_Lean_Name_toString(x_71, x_73, x_68);
x_75 = lean_mk_string_unchecked(".", 1, 1);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = lean_mk_string_unchecked("olean\?", 6, 6);
x_78 = l_Lean_Name_mkStr1(x_77);
x_79 = lean_unbox(x_72);
x_80 = l_Lean_Name_toString(x_78, x_79, x_68);
x_81 = lean_string_append(x_76, x_80);
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
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_47, 0);
lean_inc(x_89);
lean_dec(x_47);
x_90 = lean_mk_string_unchecked("oleanServer", 11, 11);
lean_inc(x_1);
x_91 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(x_1, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
lean_dec(x_89);
lean_dec(x_45);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_95 = lean_mk_string_unchecked("Lean", 4, 4);
x_96 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_97 = l_Lean_Name_mkStr2(x_95, x_96);
x_98 = lean_box(1);
x_99 = lean_unbox(x_98);
lean_inc(x_94);
x_100 = l_Lean_Name_toString(x_97, x_99, x_94);
x_101 = lean_mk_string_unchecked(".", 1, 1);
x_102 = lean_string_append(x_100, x_101);
lean_dec(x_101);
x_103 = lean_mk_string_unchecked("oleanServer\?", 12, 12);
x_104 = l_Lean_Name_mkStr1(x_103);
x_105 = lean_unbox(x_98);
x_106 = l_Lean_Name_toString(x_104, x_105, x_94);
x_107 = lean_string_append(x_102, x_106);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked(": ", 2, 2);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_string_append(x_109, x_93);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_110);
return x_91;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_91, 0);
lean_inc(x_111);
lean_dec(x_91);
x_112 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_113 = lean_mk_string_unchecked("Lean", 4, 4);
x_114 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_115 = l_Lean_Name_mkStr2(x_113, x_114);
x_116 = lean_box(1);
x_117 = lean_unbox(x_116);
lean_inc(x_112);
x_118 = l_Lean_Name_toString(x_115, x_117, x_112);
x_119 = lean_mk_string_unchecked(".", 1, 1);
x_120 = lean_string_append(x_118, x_119);
lean_dec(x_119);
x_121 = lean_mk_string_unchecked("oleanServer\?", 12, 12);
x_122 = l_Lean_Name_mkStr1(x_121);
x_123 = lean_unbox(x_116);
x_124 = l_Lean_Name_toString(x_122, x_123, x_112);
x_125 = lean_string_append(x_120, x_124);
lean_dec(x_124);
x_126 = lean_mk_string_unchecked(": ", 2, 2);
x_127 = lean_string_append(x_125, x_126);
lean_dec(x_126);
x_128 = lean_string_append(x_127, x_111);
lean_dec(x_111);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
else
{
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_130; 
lean_dec(x_89);
lean_dec(x_45);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_91);
if (x_130 == 0)
{
lean_ctor_set_tag(x_91, 0);
return x_91;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_91, 0);
lean_inc(x_131);
lean_dec(x_91);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_91, 0);
lean_inc(x_133);
lean_dec(x_91);
x_134 = lean_mk_string_unchecked("oleanPrivate", 12, 12);
lean_inc(x_1);
x_135 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(x_1, x_134);
lean_dec(x_134);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
lean_dec(x_133);
lean_dec(x_89);
lean_dec(x_45);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_139 = lean_mk_string_unchecked("Lean", 4, 4);
x_140 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_141 = l_Lean_Name_mkStr2(x_139, x_140);
x_142 = lean_box(1);
x_143 = lean_unbox(x_142);
lean_inc(x_138);
x_144 = l_Lean_Name_toString(x_141, x_143, x_138);
x_145 = lean_mk_string_unchecked(".", 1, 1);
x_146 = lean_string_append(x_144, x_145);
lean_dec(x_145);
x_147 = lean_mk_string_unchecked("oleanPrivate\?", 13, 13);
x_148 = l_Lean_Name_mkStr1(x_147);
x_149 = lean_unbox(x_142);
x_150 = l_Lean_Name_toString(x_148, x_149, x_138);
x_151 = lean_string_append(x_146, x_150);
lean_dec(x_150);
x_152 = lean_mk_string_unchecked(": ", 2, 2);
x_153 = lean_string_append(x_151, x_152);
lean_dec(x_152);
x_154 = lean_string_append(x_153, x_137);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_154);
return x_135;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_155 = lean_ctor_get(x_135, 0);
lean_inc(x_155);
lean_dec(x_135);
x_156 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_157 = lean_mk_string_unchecked("Lean", 4, 4);
x_158 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_159 = l_Lean_Name_mkStr2(x_157, x_158);
x_160 = lean_box(1);
x_161 = lean_unbox(x_160);
lean_inc(x_156);
x_162 = l_Lean_Name_toString(x_159, x_161, x_156);
x_163 = lean_mk_string_unchecked(".", 1, 1);
x_164 = lean_string_append(x_162, x_163);
lean_dec(x_163);
x_165 = lean_mk_string_unchecked("oleanPrivate\?", 13, 13);
x_166 = l_Lean_Name_mkStr1(x_165);
x_167 = lean_unbox(x_160);
x_168 = l_Lean_Name_toString(x_166, x_167, x_156);
x_169 = lean_string_append(x_164, x_168);
lean_dec(x_168);
x_170 = lean_mk_string_unchecked(": ", 2, 2);
x_171 = lean_string_append(x_169, x_170);
lean_dec(x_170);
x_172 = lean_string_append(x_171, x_155);
lean_dec(x_155);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
else
{
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_174; 
lean_dec(x_133);
lean_dec(x_89);
lean_dec(x_45);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_135);
if (x_174 == 0)
{
lean_ctor_set_tag(x_135, 0);
return x_135;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_135, 0);
lean_inc(x_175);
lean_dec(x_135);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_135, 0);
lean_inc(x_177);
lean_dec(x_135);
x_178 = lean_mk_string_unchecked("ilean", 5, 5);
x_179 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(x_1, x_178);
lean_dec(x_178);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
lean_dec(x_177);
lean_dec(x_133);
lean_dec(x_89);
lean_dec(x_45);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_183 = lean_mk_string_unchecked("Lean", 4, 4);
x_184 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_185 = l_Lean_Name_mkStr2(x_183, x_184);
x_186 = lean_box(1);
x_187 = lean_unbox(x_186);
lean_inc(x_182);
x_188 = l_Lean_Name_toString(x_185, x_187, x_182);
x_189 = lean_mk_string_unchecked(".", 1, 1);
x_190 = lean_string_append(x_188, x_189);
lean_dec(x_189);
x_191 = lean_mk_string_unchecked("ilean\?", 6, 6);
x_192 = l_Lean_Name_mkStr1(x_191);
x_193 = lean_unbox(x_186);
x_194 = l_Lean_Name_toString(x_192, x_193, x_182);
x_195 = lean_string_append(x_190, x_194);
lean_dec(x_194);
x_196 = lean_mk_string_unchecked(": ", 2, 2);
x_197 = lean_string_append(x_195, x_196);
lean_dec(x_196);
x_198 = lean_string_append(x_197, x_181);
lean_dec(x_181);
lean_ctor_set(x_179, 0, x_198);
return x_179;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_199 = lean_ctor_get(x_179, 0);
lean_inc(x_199);
lean_dec(x_179);
x_200 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_201 = lean_mk_string_unchecked("Lean", 4, 4);
x_202 = lean_mk_string_unchecked("ModuleArtifacts", 15, 15);
x_203 = l_Lean_Name_mkStr2(x_201, x_202);
x_204 = lean_box(1);
x_205 = lean_unbox(x_204);
lean_inc(x_200);
x_206 = l_Lean_Name_toString(x_203, x_205, x_200);
x_207 = lean_mk_string_unchecked(".", 1, 1);
x_208 = lean_string_append(x_206, x_207);
lean_dec(x_207);
x_209 = lean_mk_string_unchecked("ilean\?", 6, 6);
x_210 = l_Lean_Name_mkStr1(x_209);
x_211 = lean_unbox(x_204);
x_212 = l_Lean_Name_toString(x_210, x_211, x_200);
x_213 = lean_string_append(x_208, x_212);
lean_dec(x_212);
x_214 = lean_mk_string_unchecked(": ", 2, 2);
x_215 = lean_string_append(x_213, x_214);
lean_dec(x_214);
x_216 = lean_string_append(x_215, x_199);
lean_dec(x_199);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
else
{
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_218; 
lean_dec(x_177);
lean_dec(x_133);
lean_dec(x_89);
lean_dec(x_45);
x_218 = !lean_is_exclusive(x_179);
if (x_218 == 0)
{
lean_ctor_set_tag(x_179, 0);
return x_179;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_179, 0);
lean_inc(x_219);
lean_dec(x_179);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
else
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_179);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_179, 0);
x_223 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_223, 0, x_45);
lean_ctor_set(x_223, 1, x_89);
lean_ctor_set(x_223, 2, x_133);
lean_ctor_set(x_223, 3, x_177);
lean_ctor_set(x_223, 4, x_222);
lean_ctor_set(x_179, 0, x_223);
return x_179;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_179, 0);
lean_inc(x_224);
lean_dec(x_179);
x_225 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_225, 0, x_45);
lean_ctor_set(x_225, 1, x_89);
lean_ctor_set(x_225, 2, x_133);
lean_ctor_set(x_225, 3, x_177);
lean_ctor_set(x_225, 4, x_224);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
return x_226;
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
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleArtifacts() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_mk_string_unchecked("(", 1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Name_reprPrec(x_3, x_6);
x_8 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = l___private_Lean_Setup_0__Lean_reprModuleArtifacts___redArg____x40_Lean_Setup___hyg_417_(x_4);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = l_List_reverse___redArg(x_10);
x_12 = lean_mk_string_unchecked(",", 1, 1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_11, x_15);
x_17 = lean_mk_string_unchecked(")", 1, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_30 = lean_mk_string_unchecked("(", 1, 1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Name_reprPrec(x_28, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Setup_0__Lean_reprModuleArtifacts___redArg____x40_Lean_Setup___hyg_417_(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_List_reverse___redArg(x_36);
x_38 = lean_mk_string_unchecked(",", 1, 1);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(1);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_37, x_41);
x_43 = lean_mk_string_unchecked(")", 1, 1);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_30);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_unbox(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__0____x40_Lean_Setup___hyg_913_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Setup_0__Lean_reprImport___redArg____x40_Lean_Setup___hyg_34_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__1____x40_Lean_Setup___hyg_913_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_String_quote(x_2);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg____x40_Lean_Setup___hyg_913_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_176; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__0____x40_Lean_Setup___hyg_913_), 1, 0);
x_3 = lean_mk_string_unchecked("{ ", 2, 2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("name", 4, 4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked(" := ", 4, 4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__1____x40_Lean_Setup___hyg_913____boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_Name_reprPrec(x_13, x_14);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_mk_string_unchecked(",", 1, 1);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_23);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(1);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_24);
lean_ctor_set(x_137, 1, x_25);
x_138 = lean_mk_string_unchecked("isModule", 8, 8);
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_9);
x_141 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_9);
x_142 = lean_unsigned_to_nat(12u);
x_143 = lean_nat_to_int(x_142);
x_176 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_mk_string_unchecked("false", 5, 5);
x_178 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_144 = x_178;
goto block_175;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_mk_string_unchecked("true", 4, 4);
x_180 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_144 = x_180;
goto block_175;
}
block_55:
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_unbox(x_18);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
x_35 = lean_mk_string_unchecked("options", 7, 7);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
x_39 = lean_ctor_get(x_1, 5);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l___private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions___redArg____x40_Lean_Util_LeanOptions___hyg_541_(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_unbox(x_18);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_mk_string_unchecked(" }", 2, 2);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_to_int(x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_3);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_unbox(x_18);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
return x_53;
}
block_87:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_inc(x_57);
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_unbox(x_18);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_61);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_60);
lean_inc(x_23);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_23);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_25);
x_65 = lean_mk_string_unchecked("plugins", 7, 7);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_9);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_9);
x_69 = lean_ctor_get(x_1, 4);
lean_inc(x_69);
x_70 = lean_array_get_size(x_69);
x_71 = lean_nat_dec_eq(x_70, x_14);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_72 = lean_mk_string_unchecked("#[", 2, 2);
x_73 = lean_array_to_list(x_69);
lean_inc(x_23);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_23);
lean_ctor_set(x_74, 1, x_25);
x_75 = l_Std_Format_joinSep(lean_box(0), x_15, x_73, x_74);
x_76 = lean_mk_string_unchecked("]", 1, 1);
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_to_int(x_77);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_72);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Std_Format_fill(x_83);
x_26 = x_68;
x_27 = x_57;
x_28 = x_84;
goto block_55;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_69);
lean_dec(x_15);
x_85 = lean_mk_string_unchecked("#[]", 3, 3);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_26 = x_68;
x_27 = x_57;
x_28 = x_86;
goto block_55;
}
}
block_136:
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_inc(x_88);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_unbox(x_18);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_93);
x_94 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
lean_inc(x_23);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_23);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_25);
x_97 = lean_mk_string_unchecked("modules", 7, 7);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_9);
x_100 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_9);
x_101 = lean_ctor_get(x_1, 2);
lean_inc(x_101);
x_102 = lean_mk_string_unchecked("Lean.rbmapOf ", 13, 13);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_RBMap_toList___at_____private_Lean_Util_LeanOptions_0__Lean_reprLeanOptions____x40_Lean_Util_LeanOptions___hyg_541__spec__0___redArg(x_101);
lean_dec(x_101);
x_105 = l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___redArg(x_104);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Repr_addAppParen(x_106, x_14);
lean_inc(x_88);
x_108 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_108, 0, x_88);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_unbox(x_18);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_100);
lean_ctor_set(x_111, 1, x_109);
lean_inc(x_23);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_23);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_25);
x_114 = lean_mk_string_unchecked("dynlibs", 7, 7);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_9);
x_117 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_9);
x_118 = lean_ctor_get(x_1, 3);
lean_inc(x_118);
x_119 = lean_array_get_size(x_118);
x_120 = lean_nat_dec_eq(x_119, x_14);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_121 = lean_mk_string_unchecked("#[", 2, 2);
x_122 = lean_array_to_list(x_118);
lean_inc(x_23);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_23);
lean_ctor_set(x_123, 1, x_25);
lean_inc(x_15);
x_124 = l_Std_Format_joinSep(lean_box(0), x_15, x_122, x_123);
x_125 = lean_mk_string_unchecked("]", 1, 1);
x_126 = lean_unsigned_to_nat(2u);
x_127 = lean_nat_to_int(x_126);
x_128 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_128, 0, x_121);
x_129 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_125);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Std_Format_fill(x_132);
x_56 = x_117;
x_57 = x_88;
x_58 = x_133;
goto block_87;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_118);
x_134 = lean_mk_string_unchecked("#[]", 3, 3);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_56 = x_117;
x_57 = x_88;
x_58 = x_135;
goto block_87;
}
}
block_175:
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_145 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_unbox(x_18);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_147);
x_148 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_146);
lean_inc(x_23);
x_149 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_23);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_25);
x_151 = lean_mk_string_unchecked("imports", 7, 7);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
lean_inc(x_9);
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_9);
x_155 = lean_unsigned_to_nat(11u);
x_156 = lean_nat_to_int(x_155);
x_157 = lean_ctor_get(x_1, 1);
lean_inc(x_157);
x_158 = lean_array_get_size(x_157);
x_159 = lean_nat_dec_eq(x_158, x_14);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_160 = lean_mk_string_unchecked("#[", 2, 2);
x_161 = lean_array_to_list(x_157);
lean_inc(x_23);
x_162 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_162, 0, x_23);
lean_ctor_set(x_162, 1, x_25);
x_163 = l_Std_Format_joinSep(lean_box(0), x_2, x_161, x_162);
x_164 = lean_mk_string_unchecked("]", 1, 1);
x_165 = lean_unsigned_to_nat(2u);
x_166 = lean_nat_to_int(x_165);
x_167 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_167, 0, x_160);
x_168 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_163);
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_164);
x_170 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Std_Format_fill(x_171);
x_88 = x_156;
x_89 = x_154;
x_90 = x_172;
goto block_136;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_2);
x_173 = lean_mk_string_unchecked("#[]", 3, 3);
x_174 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_88 = x_156;
x_89 = x_154;
x_90 = x_174;
goto block_136;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg____x40_Lean_Setup___hyg_913_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__1____x40_Lean_Setup___hyg_913____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Setup_0__Lean_reprModuleSetup___redArg___lam__1____x40_Lean_Setup___hyg_913_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprModuleSetup() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_reprModuleSetup____x40_Lean_Setup___hyg_913____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedModuleSetup() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty(lean_box(0));
x_4 = lean_box(0);
lean_inc_n(x_3, 2);
x_5 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*6, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Setup_0__Lean_toJsonImport____x40_Lean_Setup___hyg_124_(x_5);
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
LEAN_EXPORT uint8_t l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1___lam__0___boxed), 1, 0);
x_8 = l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1(x_1, x_3);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_4, x_10, x_7);
x_12 = l___private_Lean_Setup_0__Lean_toJsonModuleArtifacts____x40_Lean_Setup___hyg_549_(x_5);
x_13 = l_Lean_RBNode_insert___at___Lean_Json_mkObj_spec__0___redArg(x_8, x_11, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_alloc_closure((void*)(l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1___lam__0___boxed), 1, 0);
x_8 = l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__2(x_1, x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("name", 4, 4);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Name_toString(x_4, x_6, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("isModule", 8, 8);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_12 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("imports", 7, 7);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_array_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_mapMUnsafe_map___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__0(x_16, x_18, x_15);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_mk_string_unchecked("modules", 7, 7);
x_24 = lean_box(0);
x_25 = l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1(x_24, x_22);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("dynlibs", 7, 7);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
x_30 = lean_array_size(x_29);
x_31 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(x_30, x_18, x_29);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("plugins", 7, 7);
x_35 = lean_ctor_get(x_1, 4);
lean_inc(x_35);
x_36 = lean_array_size(x_35);
x_37 = l_Array_mapMUnsafe_map___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__0(x_36, x_18, x_35);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_1, 5);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_41);
x_48 = lean_mk_string_unchecked("options", 7, 7);
x_49 = l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__2(x_24, x_40);
x_50 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_43);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_42);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_empty_array_with_capacity(x_17);
x_62 = l_List_flatMapTR_go___at_____private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55__spec__1(x_60, x_61);
x_63 = l_Lean_Json_mkObj(x_62);
return x_63;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_fold___at_____private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087__spec__1___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToJsonModuleSetup() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1087_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l___private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190_(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0_spec__0(x_5, x_7, x_4);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2_spec__2(x_1, x_4);
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
x_15 = l___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593_(x_6);
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
x_26 = l___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593_(x_6);
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
x_39 = l___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593_(x_6);
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
x_51 = l___private_Lean_Setup_0__Lean_fromJsonModuleArtifacts____x40_Lean_Setup___hyg_593_(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2_spec__2(x_5, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("expected a `NameMap`, got '", 27, 27);
x_8 = lean_unsigned_to_nat(80u);
x_9 = l_Lean_Json_pretty(x_3, x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("'", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4_spec__4(lean_object* x_1, lean_object* x_2) {
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
x_14 = l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4_spec__4(x_1, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_RBNode_foldM___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4_spec__4(x_5, x_4);
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
LEAN_EXPORT lean_object* l___private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("name", 4, 4);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
x_23 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
x_44 = lean_mk_string_unchecked("isModule", 8, 8);
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonImport____x40_Lean_Setup___hyg_190__spec__1(x_1, x_44);
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
x_48 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
x_65 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_66 = lean_mk_string_unchecked("Lean", 4, 4);
x_67 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
x_86 = lean_mk_string_unchecked("imports", 7, 7);
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0(x_1, x_86);
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
x_90 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
x_107 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_108 = lean_mk_string_unchecked("Lean", 4, 4);
x_109 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
x_128 = lean_mk_string_unchecked("modules", 7, 7);
lean_inc(x_1);
x_129 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_133 = lean_mk_string_unchecked("Lean", 4, 4);
x_134 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
x_149 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_150 = lean_mk_string_unchecked("Lean", 4, 4);
x_151 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
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
lean_dec(x_1);
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
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_129, 0);
lean_inc(x_169);
lean_dec(x_129);
x_170 = lean_mk_string_unchecked("dynlibs", 7, 7);
lean_inc(x_1);
x_171 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(x_1, x_170);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_175 = lean_mk_string_unchecked("Lean", 4, 4);
x_176 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
x_177 = l_Lean_Name_mkStr2(x_175, x_176);
x_178 = lean_box(1);
x_179 = lean_unbox(x_178);
lean_inc(x_174);
x_180 = l_Lean_Name_toString(x_177, x_179, x_174);
x_181 = lean_mk_string_unchecked(".", 1, 1);
x_182 = lean_string_append(x_180, x_181);
lean_dec(x_181);
x_183 = l_Lean_Name_mkStr1(x_170);
x_184 = lean_unbox(x_178);
x_185 = l_Lean_Name_toString(x_183, x_184, x_174);
x_186 = lean_string_append(x_182, x_185);
lean_dec(x_185);
x_187 = lean_mk_string_unchecked(": ", 2, 2);
x_188 = lean_string_append(x_186, x_187);
lean_dec(x_187);
x_189 = lean_string_append(x_188, x_173);
lean_dec(x_173);
lean_ctor_set(x_171, 0, x_189);
return x_171;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
lean_dec(x_171);
x_191 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_192 = lean_mk_string_unchecked("Lean", 4, 4);
x_193 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
x_194 = l_Lean_Name_mkStr2(x_192, x_193);
x_195 = lean_box(1);
x_196 = lean_unbox(x_195);
lean_inc(x_191);
x_197 = l_Lean_Name_toString(x_194, x_196, x_191);
x_198 = lean_mk_string_unchecked(".", 1, 1);
x_199 = lean_string_append(x_197, x_198);
lean_dec(x_198);
x_200 = l_Lean_Name_mkStr1(x_170);
x_201 = lean_unbox(x_195);
x_202 = l_Lean_Name_toString(x_200, x_201, x_191);
x_203 = lean_string_append(x_199, x_202);
lean_dec(x_202);
x_204 = lean_mk_string_unchecked(": ", 2, 2);
x_205 = lean_string_append(x_203, x_204);
lean_dec(x_204);
x_206 = lean_string_append(x_205, x_190);
lean_dec(x_190);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
else
{
lean_dec(x_170);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_208; 
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_171);
if (x_208 == 0)
{
lean_ctor_set_tag(x_171, 0);
return x_171;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_171, 0);
lean_inc(x_209);
lean_dec(x_171);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_171, 0);
lean_inc(x_211);
lean_dec(x_171);
x_212 = lean_mk_string_unchecked("plugins", 7, 7);
lean_inc(x_1);
x_213 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_135__spec__2(x_1, x_212);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_217 = lean_mk_string_unchecked("Lean", 4, 4);
x_218 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
x_219 = l_Lean_Name_mkStr2(x_217, x_218);
x_220 = lean_box(1);
x_221 = lean_unbox(x_220);
lean_inc(x_216);
x_222 = l_Lean_Name_toString(x_219, x_221, x_216);
x_223 = lean_mk_string_unchecked(".", 1, 1);
x_224 = lean_string_append(x_222, x_223);
lean_dec(x_223);
x_225 = l_Lean_Name_mkStr1(x_212);
x_226 = lean_unbox(x_220);
x_227 = l_Lean_Name_toString(x_225, x_226, x_216);
x_228 = lean_string_append(x_224, x_227);
lean_dec(x_227);
x_229 = lean_mk_string_unchecked(": ", 2, 2);
x_230 = lean_string_append(x_228, x_229);
lean_dec(x_229);
x_231 = lean_string_append(x_230, x_215);
lean_dec(x_215);
lean_ctor_set(x_213, 0, x_231);
return x_213;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_232 = lean_ctor_get(x_213, 0);
lean_inc(x_232);
lean_dec(x_213);
x_233 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_234 = lean_mk_string_unchecked("Lean", 4, 4);
x_235 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
x_236 = l_Lean_Name_mkStr2(x_234, x_235);
x_237 = lean_box(1);
x_238 = lean_unbox(x_237);
lean_inc(x_233);
x_239 = l_Lean_Name_toString(x_236, x_238, x_233);
x_240 = lean_mk_string_unchecked(".", 1, 1);
x_241 = lean_string_append(x_239, x_240);
lean_dec(x_240);
x_242 = l_Lean_Name_mkStr1(x_212);
x_243 = lean_unbox(x_237);
x_244 = l_Lean_Name_toString(x_242, x_243, x_233);
x_245 = lean_string_append(x_241, x_244);
lean_dec(x_244);
x_246 = lean_mk_string_unchecked(": ", 2, 2);
x_247 = lean_string_append(x_245, x_246);
lean_dec(x_246);
x_248 = lean_string_append(x_247, x_232);
lean_dec(x_232);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
}
else
{
lean_dec(x_212);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_250; 
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_213);
if (x_250 == 0)
{
lean_ctor_set_tag(x_213, 0);
return x_213;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_213, 0);
lean_inc(x_251);
lean_dec(x_213);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_251);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_213, 0);
lean_inc(x_253);
lean_dec(x_213);
x_254 = lean_mk_string_unchecked("options", 7, 7);
x_255 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4(x_1, x_254);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_256; 
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_259 = lean_mk_string_unchecked("Lean", 4, 4);
x_260 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
x_261 = l_Lean_Name_mkStr2(x_259, x_260);
x_262 = lean_box(1);
x_263 = lean_unbox(x_262);
lean_inc(x_258);
x_264 = l_Lean_Name_toString(x_261, x_263, x_258);
x_265 = lean_mk_string_unchecked(".", 1, 1);
x_266 = lean_string_append(x_264, x_265);
lean_dec(x_265);
x_267 = l_Lean_Name_mkStr1(x_254);
x_268 = lean_unbox(x_262);
x_269 = l_Lean_Name_toString(x_267, x_268, x_258);
x_270 = lean_string_append(x_266, x_269);
lean_dec(x_269);
x_271 = lean_mk_string_unchecked(": ", 2, 2);
x_272 = lean_string_append(x_270, x_271);
lean_dec(x_271);
x_273 = lean_string_append(x_272, x_257);
lean_dec(x_257);
lean_ctor_set(x_255, 0, x_273);
return x_255;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_274 = lean_ctor_get(x_255, 0);
lean_inc(x_274);
lean_dec(x_255);
x_275 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_toJsonImport___lam__0____x40_Lean_Setup___hyg_124____boxed), 1, 0);
x_276 = lean_mk_string_unchecked("Lean", 4, 4);
x_277 = lean_mk_string_unchecked("ModuleSetup", 11, 11);
x_278 = l_Lean_Name_mkStr2(x_276, x_277);
x_279 = lean_box(1);
x_280 = lean_unbox(x_279);
lean_inc(x_275);
x_281 = l_Lean_Name_toString(x_278, x_280, x_275);
x_282 = lean_mk_string_unchecked(".", 1, 1);
x_283 = lean_string_append(x_281, x_282);
lean_dec(x_282);
x_284 = l_Lean_Name_mkStr1(x_254);
x_285 = lean_unbox(x_279);
x_286 = l_Lean_Name_toString(x_284, x_285, x_275);
x_287 = lean_string_append(x_283, x_286);
lean_dec(x_286);
x_288 = lean_mk_string_unchecked(": ", 2, 2);
x_289 = lean_string_append(x_287, x_288);
lean_dec(x_288);
x_290 = lean_string_append(x_289, x_274);
lean_dec(x_274);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
else
{
lean_dec(x_254);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_292; 
lean_dec(x_253);
lean_dec(x_211);
lean_dec(x_169);
lean_dec(x_127);
lean_dec(x_85);
lean_dec(x_43);
x_292 = !lean_is_exclusive(x_255);
if (x_292 == 0)
{
lean_ctor_set_tag(x_255, 0);
return x_255;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_255, 0);
lean_inc(x_293);
lean_dec(x_255);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
else
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_255);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_296 = lean_ctor_get(x_255, 0);
x_297 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_297, 0, x_43);
lean_ctor_set(x_297, 1, x_127);
lean_ctor_set(x_297, 2, x_169);
lean_ctor_set(x_297, 3, x_211);
lean_ctor_set(x_297, 4, x_253);
lean_ctor_set(x_297, 5, x_296);
x_298 = lean_unbox(x_85);
lean_dec(x_85);
lean_ctor_set_uint8(x_297, sizeof(void*)*6, x_298);
lean_ctor_set(x_255, 0, x_297);
return x_255;
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_255, 0);
lean_inc(x_299);
lean_dec(x_255);
x_300 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_300, 0, x_43);
lean_ctor_set(x_300, 1, x_127);
lean_ctor_set(x_300, 2, x_169);
lean_ctor_set(x_300, 3, x_211);
lean_ctor_set(x_300, 4, x_253);
lean_ctor_set(x_300, 5, x_299);
x_301 = lean_unbox(x_85);
lean_dec(x_85);
lean_ctor_set_uint8(x_300, sizeof(void*)*6, x_301);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_300);
return x_302;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209__spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFromJsonModuleSetup() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_16; 
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
x_16 = l_Lean_Json_parse(x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_7 = x_17;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Setup_0__Lean_fromJsonModuleSetup____x40_Lean_Setup___hyg_1209_(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_7 = x_20;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("failed to load header from ", 27, 27);
x_9 = lean_string_append(x_8, x_1);
x_10 = lean_mk_string_unchecked(": ", 2, 2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = lean_string_append(x_11, x_7);
lean_dec(x_7);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
if (lean_is_scalar(x_6)) {
 x_14 = lean_alloc_ctor(1, 2, 0);
} else {
 x_14 = x_6;
 lean_ctor_set_tag(x_14, 1);
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
else
{
uint8_t x_23; 
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
LEAN_EXPORT lean_object* l_Lean_ModuleSetup_load___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ModuleSetup_load(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LeanOptions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Setup(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LeanOptions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instReprImport = _init_l_Lean_instReprImport();
lean_mark_persistent(l_Lean_instReprImport);
l_Lean_instInhabitedImport = _init_l_Lean_instInhabitedImport();
lean_mark_persistent(l_Lean_instInhabitedImport);
l_Lean_instToJsonImport = _init_l_Lean_instToJsonImport();
lean_mark_persistent(l_Lean_instToJsonImport);
l_Lean_instFromJsonImport = _init_l_Lean_instFromJsonImport();
lean_mark_persistent(l_Lean_instFromJsonImport);
l_Lean_instCoeNameImport = _init_l_Lean_instCoeNameImport();
lean_mark_persistent(l_Lean_instCoeNameImport);
l_Lean_instToStringImport = _init_l_Lean_instToStringImport();
lean_mark_persistent(l_Lean_instToStringImport);
l_Lean_instReprModuleArtifacts = _init_l_Lean_instReprModuleArtifacts();
lean_mark_persistent(l_Lean_instReprModuleArtifacts);
l_Lean_instInhabitedModuleArtifacts = _init_l_Lean_instInhabitedModuleArtifacts();
lean_mark_persistent(l_Lean_instInhabitedModuleArtifacts);
l_Lean_instToJsonModuleArtifacts = _init_l_Lean_instToJsonModuleArtifacts();
lean_mark_persistent(l_Lean_instToJsonModuleArtifacts);
l_Lean_instFromJsonModuleArtifacts = _init_l_Lean_instFromJsonModuleArtifacts();
lean_mark_persistent(l_Lean_instFromJsonModuleArtifacts);
l_Lean_instReprModuleSetup = _init_l_Lean_instReprModuleSetup();
lean_mark_persistent(l_Lean_instReprModuleSetup);
l_Lean_instInhabitedModuleSetup = _init_l_Lean_instInhabitedModuleSetup();
lean_mark_persistent(l_Lean_instInhabitedModuleSetup);
l_Lean_instToJsonModuleSetup = _init_l_Lean_instToJsonModuleSetup();
lean_mark_persistent(l_Lean_instToJsonModuleSetup);
l_Lean_instFromJsonModuleSetup = _init_l_Lean_instFromJsonModuleSetup();
lean_mark_persistent(l_Lean_instFromJsonModuleSetup);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
