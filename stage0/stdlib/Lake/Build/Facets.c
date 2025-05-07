// Lean compiler output
// Module: Lake.Build.Facets
// Imports: Lake.Build.Data Lake.Build.Job.Basic Lake.Config.Dynlib
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedModuleDeps;
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_Module_coExportFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps____x40_Lake_Build_Facets___hyg_51_(lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_Module_cFacet;
LEAN_EXPORT lean_object* l_Lake_ExternLib_dynlibFacet;
LEAN_EXPORT lean_object* l_Lake_Module_ileanFacet;
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_depsFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_extraDepFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleFacet____x40_Lake_Build_Facets___hyg_138_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleFacet____x40_Lake_Build_Facets___hyg_138____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg____x40_Lake_Config_Dynlib___hyg_60_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_Module_coNoExportFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps____x40_Lake_Build_Facets___hyg_51____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExe_exeFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps___redArg____x40_Lake_Build_Facets___hyg_51_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacet;
LEAN_EXPORT lean_object* l_Lake_Module_leanArtsFacet;
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprModuleDeps;
LEAN_EXPORT lean_object* l_Lake_Module_bcFacet;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps___redArg___lam__0____x40_Lake_Build_Facets___hyg_51_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacet;
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacet;
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacet;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacet;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_Module_coFacet;
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_bcoFacet;
LEAN_EXPORT lean_object* l_Lake_Module_oExportFacet;
LEAN_EXPORT lean_object* l_Lake_LeanExe_defaultFacet;
LEAN_EXPORT lean_object* l_Lake_Package_releaseFacet;
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_staticFacet;
LEAN_EXPORT lean_object* l_Lake_Module_oNoExportFacet;
LEAN_EXPORT lean_object* l_Lake_Package_reservoirBarrelFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacet;
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleFacet___redArg____x40_Lake_Build_Facets___hyg_138_(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ExternLib_defaultFacet;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_sharedFacet;
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Module_oleanFacet;
LEAN_EXPORT lean_object* l_Lake_Module_oFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optReleaseFacet;
LEAN_EXPORT lean_object* l_Lake_Package_optReservoirBarrelFacet;
static lean_object* _init_l_Lake_instInhabitedModuleDeps() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty(lean_box(0));
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps___redArg___lam__0____x40_Lake_Build_Facets___hyg_51_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg____x40_Lake_Config_Dynlib___hyg_60_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps___redArg____x40_Lake_Build_Facets___hyg_51_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_29; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Build_Facets_0__Lake_reprModuleDeps___redArg___lam__0____x40_Lake_Build_Facets___hyg_51_), 1, 0);
x_3 = lean_mk_string_unchecked("{ ", 2, 2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("dynlibs", 7, 7);
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
x_11 = lean_unsigned_to_nat(11u);
x_12 = lean_nat_to_int(x_11);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_array_get_size(x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_eq(x_67, x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_mk_string_unchecked("#[", 2, 2);
x_71 = lean_array_to_list(x_66);
x_72 = lean_mk_string_unchecked(",", 1, 1);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_box(1);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_2);
x_76 = l_Std_Format_joinSep(lean_box(0), x_2, x_71, x_75);
x_77 = lean_mk_string_unchecked("]", 1, 1);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_to_int(x_78);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_70);
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
x_85 = l_Std_Format_fill(x_84);
x_29 = x_85;
goto block_65;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
x_86 = lean_mk_string_unchecked("#[]", 3, 3);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_29 = x_87;
goto block_65;
}
block_28:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_13);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(" }", 2, 2);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_13);
return x_27;
}
block_65:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_inc(x_12);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_mk_string_unchecked(",", 1, 1);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_36);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(1);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("plugins", 7, 7);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_array_get_size(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_48 = lean_mk_string_unchecked("#[", 2, 2);
x_49 = lean_array_to_list(x_44);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_38);
x_51 = l_Std_Format_joinSep(lean_box(0), x_2, x_49, x_50);
x_52 = lean_mk_string_unchecked("]", 1, 1);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_48);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Std_Format_fill(x_59);
x_61 = lean_unbox(x_31);
x_13 = x_61;
x_14 = x_43;
x_15 = x_60;
goto block_28;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_2);
x_62 = lean_mk_string_unchecked("#[]", 3, 3);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_unbox(x_31);
x_13 = x_64;
x_14 = x_43;
x_15 = x_63;
goto block_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps____x40_Lake_Build_Facets___hyg_51_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Facets_0__Lake_reprModuleDeps___redArg____x40_Lake_Build_Facets___hyg_51_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleDeps____x40_Lake_Build_Facets___hyg_51____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Facets_0__Lake_reprModuleDeps____x40_Lake_Build_Facets___hyg_51_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprModuleDeps() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Facets_0__Lake_reprModuleDeps____x40_Lake_Build_Facets___hyg_51____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleFacet___redArg____x40_Lake_Build_Facets___hyg_138_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("name", 4, 4);
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
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Name_reprPrec(x_1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked(",", 1, 1);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("data_eq", 7, 7);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
x_28 = lean_mk_string_unchecked("_", 1, 1);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_mk_string_unchecked(" }", 2, 2);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_2);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_unbox(x_15);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
return x_39;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleFacet____x40_Lake_Build_Facets___hyg_138_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Facets_0__Lake_reprModuleFacet___redArg____x40_Lake_Build_Facets___hyg_138_(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Facets_0__Lake_reprModuleFacet____x40_Lake_Build_Facets___hyg_138____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Build_Facets_0__Lake_reprModuleFacet____x40_Lake_Build_Facets___hyg_138_(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Build_Facets_0__Lake_reprModuleFacet____x40_Lake_Build_Facets___hyg_138____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprModuleFacet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lake_Build_Facets_0__Lake_reprModuleFacet____x40_Lake_Build_Facets___hyg_138____boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instCoeDepNameModuleFacetOfFamilyOutFacetOut(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_depsFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("deps", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_leanArtsFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("leanArts", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oleanFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("olean", 5, 5);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_ileanFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("ilean", 5, 5);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_cFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("c", 1, 1);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_bcFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("bc", 2, 2);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_coFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("c", 1, 1);
x_3 = lean_mk_string_unchecked("o", 1, 1);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_coExportFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("c", 1, 1);
x_3 = lean_mk_string_unchecked("o", 1, 1);
x_4 = lean_mk_string_unchecked("export", 6, 6);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Module_coNoExportFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("c", 1, 1);
x_3 = lean_mk_string_unchecked("o", 1, 1);
x_4 = lean_mk_string_unchecked("noexport", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Module_bcoFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("bc", 2, 2);
x_3 = lean_mk_string_unchecked("o", 1, 1);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_oFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("o", 1, 1);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Module_oExportFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("o", 1, 1);
x_3 = lean_mk_string_unchecked("export", 6, 6);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Module_oNoExportFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
x_2 = lean_mk_string_unchecked("o", 1, 1);
x_3 = lean_mk_string_unchecked("noexport", 8, 8);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = lean_mk_string_unchecked("optCache", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = lean_mk_string_unchecked("cache", 5, 5);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optReservoirBarrelFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = lean_mk_string_unchecked("optBarrel", 9, 9);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_reservoirBarrelFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = lean_mk_string_unchecked("barrel", 6, 6);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = lean_mk_string_unchecked("optRelease", 10, 10);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_optReleaseFacet() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_optGitHubReleaseFacet;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = lean_mk_string_unchecked("release", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_releaseFacet() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_gitHubReleaseFacet;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
x_2 = lean_mk_string_unchecked("extraDep", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = lean_mk_string_unchecked("default", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = lean_mk_string_unchecked("leanArts", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = lean_mk_string_unchecked("static", 6, 6);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = lean_mk_string_unchecked("static", 6, 6);
x_3 = lean_mk_string_unchecked("export", 6, 6);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = lean_mk_string_unchecked("shared", 6, 6);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
x_2 = lean_mk_string_unchecked("extraDep", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExe_defaultFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lean_exe", 8, 8);
x_2 = lean_mk_string_unchecked("default", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExe_exeFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("lean_exe", 8, 8);
x_2 = lean_mk_string_unchecked("exe", 3, 3);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ExternLib_defaultFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("extern_lib", 10, 10);
x_2 = lean_mk_string_unchecked("default", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ExternLib_staticFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("extern_lib", 10, 10);
x_2 = lean_mk_string_unchecked("static", 6, 6);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ExternLib_sharedFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("extern_lib", 10, 10);
x_2 = lean_mk_string_unchecked("shared", 6, 6);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_ExternLib_dynlibFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("extern_lib", 10, 10);
x_2 = lean_mk_string_unchecked("dynlib", 6, 6);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_InputFile_defaultFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("input_file", 10, 10);
x_2 = lean_mk_string_unchecked("default", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_InputDir_defaultFacet() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("input_dir", 9, 9);
x_2 = lean_mk_string_unchecked("default", 7, 7);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Lake_Build_Data(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Facets(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedModuleDeps = _init_l_Lake_instInhabitedModuleDeps();
lean_mark_persistent(l_Lake_instInhabitedModuleDeps);
l_Lake_instReprModuleDeps = _init_l_Lake_instReprModuleDeps();
lean_mark_persistent(l_Lake_instReprModuleDeps);
l_Lake_Module_depsFacet = _init_l_Lake_Module_depsFacet();
lean_mark_persistent(l_Lake_Module_depsFacet);
l_Lake_Module_leanArtsFacet = _init_l_Lake_Module_leanArtsFacet();
lean_mark_persistent(l_Lake_Module_leanArtsFacet);
l_Lake_Module_oleanFacet = _init_l_Lake_Module_oleanFacet();
lean_mark_persistent(l_Lake_Module_oleanFacet);
l_Lake_Module_ileanFacet = _init_l_Lake_Module_ileanFacet();
lean_mark_persistent(l_Lake_Module_ileanFacet);
l_Lake_Module_cFacet = _init_l_Lake_Module_cFacet();
lean_mark_persistent(l_Lake_Module_cFacet);
l_Lake_Module_bcFacet = _init_l_Lake_Module_bcFacet();
lean_mark_persistent(l_Lake_Module_bcFacet);
l_Lake_Module_coFacet = _init_l_Lake_Module_coFacet();
lean_mark_persistent(l_Lake_Module_coFacet);
l_Lake_Module_coExportFacet = _init_l_Lake_Module_coExportFacet();
lean_mark_persistent(l_Lake_Module_coExportFacet);
l_Lake_Module_coNoExportFacet = _init_l_Lake_Module_coNoExportFacet();
lean_mark_persistent(l_Lake_Module_coNoExportFacet);
l_Lake_Module_bcoFacet = _init_l_Lake_Module_bcoFacet();
lean_mark_persistent(l_Lake_Module_bcoFacet);
l_Lake_Module_oFacet = _init_l_Lake_Module_oFacet();
lean_mark_persistent(l_Lake_Module_oFacet);
l_Lake_Module_oExportFacet = _init_l_Lake_Module_oExportFacet();
lean_mark_persistent(l_Lake_Module_oExportFacet);
l_Lake_Module_oNoExportFacet = _init_l_Lake_Module_oNoExportFacet();
lean_mark_persistent(l_Lake_Module_oNoExportFacet);
l_Lake_Package_optBuildCacheFacet = _init_l_Lake_Package_optBuildCacheFacet();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacet);
l_Lake_Package_buildCacheFacet = _init_l_Lake_Package_buildCacheFacet();
lean_mark_persistent(l_Lake_Package_buildCacheFacet);
l_Lake_Package_optReservoirBarrelFacet = _init_l_Lake_Package_optReservoirBarrelFacet();
lean_mark_persistent(l_Lake_Package_optReservoirBarrelFacet);
l_Lake_Package_reservoirBarrelFacet = _init_l_Lake_Package_reservoirBarrelFacet();
lean_mark_persistent(l_Lake_Package_reservoirBarrelFacet);
l_Lake_Package_optGitHubReleaseFacet = _init_l_Lake_Package_optGitHubReleaseFacet();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacet);
l_Lake_Package_optReleaseFacet = _init_l_Lake_Package_optReleaseFacet();
lean_mark_persistent(l_Lake_Package_optReleaseFacet);
l_Lake_Package_gitHubReleaseFacet = _init_l_Lake_Package_gitHubReleaseFacet();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacet);
l_Lake_Package_releaseFacet = _init_l_Lake_Package_releaseFacet();
lean_mark_persistent(l_Lake_Package_releaseFacet);
l_Lake_Package_extraDepFacet = _init_l_Lake_Package_extraDepFacet();
lean_mark_persistent(l_Lake_Package_extraDepFacet);
l_Lake_LeanLib_defaultFacet = _init_l_Lake_LeanLib_defaultFacet();
lean_mark_persistent(l_Lake_LeanLib_defaultFacet);
l_Lake_LeanLib_leanArtsFacet = _init_l_Lake_LeanLib_leanArtsFacet();
lean_mark_persistent(l_Lake_LeanLib_leanArtsFacet);
l_Lake_LeanLib_staticFacet = _init_l_Lake_LeanLib_staticFacet();
lean_mark_persistent(l_Lake_LeanLib_staticFacet);
l_Lake_LeanLib_staticExportFacet = _init_l_Lake_LeanLib_staticExportFacet();
lean_mark_persistent(l_Lake_LeanLib_staticExportFacet);
l_Lake_LeanLib_sharedFacet = _init_l_Lake_LeanLib_sharedFacet();
lean_mark_persistent(l_Lake_LeanLib_sharedFacet);
l_Lake_LeanLib_extraDepFacet = _init_l_Lake_LeanLib_extraDepFacet();
lean_mark_persistent(l_Lake_LeanLib_extraDepFacet);
l_Lake_LeanExe_defaultFacet = _init_l_Lake_LeanExe_defaultFacet();
lean_mark_persistent(l_Lake_LeanExe_defaultFacet);
l_Lake_LeanExe_exeFacet = _init_l_Lake_LeanExe_exeFacet();
lean_mark_persistent(l_Lake_LeanExe_exeFacet);
l_Lake_ExternLib_defaultFacet = _init_l_Lake_ExternLib_defaultFacet();
lean_mark_persistent(l_Lake_ExternLib_defaultFacet);
l_Lake_ExternLib_staticFacet = _init_l_Lake_ExternLib_staticFacet();
lean_mark_persistent(l_Lake_ExternLib_staticFacet);
l_Lake_ExternLib_sharedFacet = _init_l_Lake_ExternLib_sharedFacet();
lean_mark_persistent(l_Lake_ExternLib_sharedFacet);
l_Lake_ExternLib_dynlibFacet = _init_l_Lake_ExternLib_dynlibFacet();
lean_mark_persistent(l_Lake_ExternLib_dynlibFacet);
l_Lake_InputFile_defaultFacet = _init_l_Lake_InputFile_defaultFacet();
lean_mark_persistent(l_Lake_InputFile_defaultFacet);
l_Lake_InputDir_defaultFacet = _init_l_Lake_InputDir_defaultFacet();
lean_mark_persistent(l_Lake_InputDir_defaultFacet);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
