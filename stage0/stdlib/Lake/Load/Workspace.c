// Lean compiler output
// Module: Lake.Load.Workspace
// Imports: Lake.Load.Resolve Lake.Build.InitFacets
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
lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterializeCore___elam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___elam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_materializeDeps___elam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_validateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0(uint8_t, lean_object*);
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*, lean_object*);
extern lean_object* l_Lake_initFacetConfigs;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__1___redArg(lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_Lake_Env_leanSearchPath(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lake_Workspace_materializeDeps_spec__10(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_writeManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadWorkspaceRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_searchPathRef;
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_Lake_Env_leanSearchPath(x_5);
x_7 = lean_st_ref_set(x_4, x_6, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("[root]", 6, 6);
lean_inc(x_1);
x_10 = l_Lake_loadPackageCore(x_9, x_1, x_2, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = l_Array_empty(lean_box(0));
x_23 = lean_box(0);
x_24 = l_Lake_initFacetConfigs;
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_1);
lean_ctor_set(x_11, 0, x_25);
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_10);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_1, 9);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_Workspace_addFacetsFromEnv(x_26, x_27, x_25);
lean_dec(x_27);
x_29 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_28, x_14);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_11, 0, x_31);
lean_ctor_set(x_29, 0, x_11);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_11, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_io_error_to_string(x_36);
x_38 = lean_box(3);
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
x_41 = lean_array_get_size(x_17);
x_42 = lean_array_push(x_17, x_39);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_42);
lean_ctor_set(x_11, 0, x_41);
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 0, x_11);
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_io_error_to_string(x_43);
x_46 = lean_box(3);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_array_get_size(x_17);
x_50 = lean_array_push(x_17, x_47);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_50);
lean_ctor_set(x_11, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_11, 1);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_dec(x_12);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = l_Array_empty(lean_box(0));
x_57 = lean_box(0);
x_58 = l_Lake_initFacetConfigs;
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
lean_ctor_set(x_59, 5, x_58);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_60; 
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_10, 0, x_60);
return x_10;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_10);
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_ctor_get(x_1, 9);
lean_inc(x_62);
lean_dec(x_1);
x_63 = l_Lake_Workspace_addFacetsFromEnv(x_61, x_62, x_59);
lean_dec(x_62);
x_64 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_63, x_14);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_52);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
x_73 = lean_io_error_to_string(x_70);
x_74 = lean_box(3);
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_unbox(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_76);
x_77 = lean_array_get_size(x_52);
x_78 = lean_array_push(x_52, x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_72;
 lean_ctor_set_tag(x_80, 0);
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_71);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_10, 1);
lean_inc(x_81);
lean_dec(x_10);
x_82 = lean_ctor_get(x_11, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_83 = x_11;
} else {
 lean_dec_ref(x_11);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_12, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_12, 1);
lean_inc(x_85);
lean_dec(x_12);
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
x_87 = l_Array_empty(lean_box(0));
x_88 = lean_box(0);
x_89 = l_Lake_initFacetConfigs;
x_90 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_5);
lean_ctor_set(x_90, 2, x_86);
lean_ctor_set(x_90, 3, x_87);
lean_ctor_set(x_90, 4, x_88);
lean_ctor_set(x_90, 5, x_89);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_81);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
lean_dec(x_85);
x_94 = lean_ctor_get(x_1, 9);
lean_inc(x_94);
lean_dec(x_1);
x_95 = l_Lake_Workspace_addFacetsFromEnv(x_93, x_94, x_90);
lean_dec(x_94);
x_96 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_95, x_81);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_83;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_82);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_104 = x_96;
} else {
 lean_dec_ref(x_96);
 x_104 = lean_box(0);
}
x_105 = lean_io_error_to_string(x_102);
x_106 = lean_box(3);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
x_109 = lean_array_get_size(x_82);
x_110 = lean_array_push(x_82, x_107);
if (lean_is_scalar(x_83)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_83;
 lean_ctor_set_tag(x_111, 1);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_104)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_104;
 lean_ctor_set_tag(x_112, 0);
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_103);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_5);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_10);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_10, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_11);
if (x_115 == 0)
{
return x_10;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_11, 0);
x_117 = lean_ctor_get(x_11, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_11);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_10, 0, x_118);
return x_10;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_10, 1);
lean_inc(x_119);
lean_dec(x_10);
x_120 = lean_ctor_get(x_11, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_11, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_122 = x_11;
} else {
 lean_dec_ref(x_11);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_119);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_2, x_1, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspace___elam__1___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lake_Workspace_updateAndMaterializeCore___at___Lake_Workspace_updateAndMaterialize_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_10);
x_12 = l_Lake_Workspace_writeManifest(x_10, x_11, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_free_object(x_12);
x_21 = lean_box(0);
x_22 = lean_usize_of_nat(x_17);
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
lean_inc(x_10);
x_24 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1(x_16, x_22, x_23, x_21, x_10, x_1, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_10);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_10, 3);
lean_inc(x_34);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_36, x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_41 = lean_box(0);
x_42 = lean_usize_of_nat(x_35);
x_43 = lean_usize_of_nat(x_36);
lean_dec(x_36);
lean_inc(x_10);
x_44 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterialize_spec__1_spec__1(x_34, x_42, x_43, x_41, x_10, x_1, x_33);
lean_dec(x_34);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_10);
x_52 = lean_ctor_get(x_12, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_io_error_to_string(x_52);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = lean_apply_2(x_1, x_56, x_53);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_7);
if (x_65 == 0)
{
return x_7;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_118; lean_object* x_119; lean_object* x_127; uint8_t x_128; 
x_8 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___elam__0___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___elam__1___boxed), 3, 0);
x_10 = lean_alloc_closure((void*)(l_Lake_Workspace_updateAndMaterializeCore___elam__1___boxed), 3, 0);
x_127 = lean_ctor_get(x_3, 3);
lean_inc(x_127);
x_128 = l_Array_isEmpty___redArg(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_129 = lean_ctor_get(x_3, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 3);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_System_FilePath_normalize(x_132);
x_134 = l_Lake_mkRelPathString(x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___Lake_Workspace_materializeDeps_spec__10(x_129, x_135);
lean_dec(x_135);
lean_dec(x_129);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_mk_string_unchecked("manifest out of date: packages directory changed; use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)", 146, 146);
x_138 = lean_box(2);
x_139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_139, 0, x_137);
x_140 = lean_unbox(x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_140);
lean_inc(x_1);
x_141 = lean_apply_2(x_1, x_139, x_7);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_118 = x_1;
x_119 = x_142;
goto block_126;
}
else
{
x_118 = x_1;
x_119 = x_7;
goto block_126;
}
}
else
{
x_118 = x_1;
x_119 = x_7;
goto block_126;
}
block_26:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_box(x_5);
lean_inc_n(x_18, 2);
lean_inc_n(x_8, 3);
x_20 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___elam__6___boxed), 18, 13);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_8);
lean_closure_set(x_20, 3, x_10);
lean_closure_set(x_20, 4, x_8);
lean_closure_set(x_20, 5, x_13);
lean_closure_set(x_20, 6, x_18);
lean_closure_set(x_20, 7, x_18);
lean_closure_set(x_20, 8, x_18);
lean_closure_set(x_20, 9, x_12);
lean_closure_set(x_20, 10, x_8);
lean_closure_set(x_20, 11, x_9);
lean_closure_set(x_20, 12, x_8);
x_21 = l_Lake_Workspace_addPackage(x_14, x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_closure((void*)(l_Lake_Workspace_materializeDeps___elam__0___at___Lake_Workspace_materializeDeps_spec__0), 7, 1);
lean_closure_set(x_24, 0, x_20);
x_25 = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___Lake_Workspace_materializeDeps_spec__5(x_24, x_21, x_22, x_23, x_11, x_15);
return x_25;
}
block_49:
{
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = l_Array_isEmpty___redArg(x_27);
lean_dec(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_34 = lean_mk_string_unchecked("missing manifest; use `lake update` to generate one", 51, 51);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_apply_2(x_28, x_36, x_31);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
x_11 = x_28;
x_12 = x_29;
x_13 = x_32;
x_14 = x_30;
x_15 = x_31;
x_16 = x_46;
goto block_26;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_27);
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
x_11 = x_28;
x_12 = x_29;
x_13 = x_32;
x_14 = x_30;
x_15 = x_31;
x_16 = x_48;
goto block_26;
}
}
block_63:
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_array_get_size(x_6);
x_58 = lean_nat_dec_lt(x_53, x_57);
if (x_58 == 0)
{
lean_dec(x_57);
x_27 = x_51;
x_28 = x_50;
x_29 = x_52;
x_30 = x_54;
x_31 = x_55;
x_32 = x_56;
goto block_49;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
x_27 = x_51;
x_28 = x_50;
x_29 = x_52;
x_30 = x_54;
x_31 = x_55;
x_32 = x_56;
goto block_49;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; 
x_60 = lean_usize_of_nat(x_53);
x_61 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_62 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_6, x_60, x_61, x_56);
x_27 = x_51;
x_28 = x_50;
x_29 = x_52;
x_30 = x_54;
x_31 = x_55;
x_32 = x_62;
goto block_49;
}
}
}
block_104:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 9);
lean_inc(x_70);
lean_inc(x_64);
lean_inc(x_68);
x_71 = l_Lake_validateManifest(x_68, x_70, x_64, x_66);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
x_74 = l_Lake_defaultLakeDir;
x_75 = l_Lake_joinRelative(x_73, x_74);
x_76 = lean_mk_string_unchecked("package-overrides.json", 22, 22);
x_77 = l_Lake_joinRelative(x_75, x_76);
lean_dec(x_76);
x_78 = l_Lake_Manifest_tryLoadEntries(x_77, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_array_get_size(x_79);
x_82 = lean_nat_dec_lt(x_67, x_81);
if (x_82 == 0)
{
lean_dec(x_81);
lean_dec(x_79);
x_50 = x_64;
x_51 = x_70;
x_52 = x_65;
x_53 = x_67;
x_54 = x_69;
x_55 = x_80;
x_56 = x_68;
goto block_63;
}
else
{
uint8_t x_83; 
x_83 = lean_nat_dec_le(x_81, x_81);
if (x_83 == 0)
{
lean_dec(x_81);
lean_dec(x_79);
x_50 = x_64;
x_51 = x_70;
x_52 = x_65;
x_53 = x_67;
x_54 = x_69;
x_55 = x_80;
x_56 = x_68;
goto block_63;
}
else
{
size_t x_84; size_t x_85; lean_object* x_86; 
x_84 = lean_usize_of_nat(x_67);
x_85 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_86 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_79, x_84, x_85, x_68);
lean_dec(x_79);
x_50 = x_64;
x_51 = x_70;
x_52 = x_65;
x_53 = x_67;
x_54 = x_69;
x_55 = x_80;
x_56 = x_86;
goto block_63;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_dec(x_78);
x_89 = lean_io_error_to_string(x_87);
x_90 = lean_box(3);
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_92);
x_93 = lean_apply_2(x_64, x_91, x_88);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = lean_box(0);
lean_ctor_set_tag(x_93, 1);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_71);
if (x_100 == 0)
{
return x_71;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_71, 0);
x_102 = lean_ctor_get(x_71, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_71);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_117:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_box(0);
x_109 = lean_ctor_get(x_3, 3);
lean_inc(x_109);
lean_dec(x_3);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_array_get_size(x_109);
x_112 = lean_nat_dec_lt(x_110, x_111);
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec(x_109);
x_64 = x_105;
x_65 = x_107;
x_66 = x_106;
x_67 = x_110;
x_68 = x_108;
goto block_104;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_111, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_109);
x_64 = x_105;
x_65 = x_107;
x_66 = x_106;
x_67 = x_110;
x_68 = x_108;
goto block_104;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
x_114 = lean_usize_of_nat(x_110);
x_115 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_116 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_materializeDeps_spec__9(x_109, x_114, x_115, x_108);
lean_dec(x_109);
x_64 = x_105;
x_65 = x_107;
x_66 = x_106;
x_67 = x_110;
x_68 = x_116;
goto block_104;
}
}
}
block_126:
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_3, 2);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_2, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 3);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_System_FilePath_normalize(x_123);
x_105 = x_118;
x_106 = x_119;
x_107 = x_124;
goto block_117;
}
else
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
lean_dec(x_120);
x_105 = x_118;
x_106 = x_119;
x_107 = x_125;
goto block_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___redArg(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_4 = lean_ctor_get(x_1, 7);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 9);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*12);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*12 + 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*12 + 2);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_mk_empty_array_with_capacity(x_39);
x_41 = l_Lake_loadWorkspaceRoot(x_1, x_40, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_array_get_size(x_45);
x_47 = lean_nat_dec_lt(x_39, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
x_9 = x_44;
x_10 = x_43;
goto block_38;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
x_9 = x_44;
x_10 = x_43;
goto block_38;
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_box(0);
x_50 = lean_usize_of_nat(x_39);
x_51 = lean_usize_of_nat(x_46);
lean_dec(x_46);
lean_inc(x_2);
x_52 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_45, x_50, x_51, x_49, x_2, x_43);
lean_dec(x_45);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_9 = x_44;
x_10 = x_53;
goto block_38;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_41, 1);
x_56 = lean_ctor_get(x_41, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_dec(x_42);
x_58 = lean_array_get_size(x_57);
x_59 = lean_nat_dec_lt(x_39, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_60 = lean_box(0);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_60);
return x_41;
}
else
{
uint8_t x_61; 
lean_free_object(x_41);
x_61 = lean_nat_dec_le(x_58, x_58);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_62 = l_Lake_loadWorkspace___elam__1___redArg(x_55);
return x_62;
}
else
{
lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_box(0);
x_64 = lean_usize_of_nat(x_39);
x_65 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_66 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_57, x_64, x_65, x_63, x_2, x_55);
lean_dec(x_57);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lake_loadWorkspace___elam__1___redArg(x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_41, 1);
lean_inc(x_69);
lean_dec(x_41);
x_70 = lean_ctor_get(x_42, 1);
lean_inc(x_70);
lean_dec(x_42);
x_71 = lean_array_get_size(x_70);
x_72 = lean_nat_dec_lt(x_39, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_2);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
return x_74;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_71, x_71);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_2);
x_76 = l_Lake_loadWorkspace___elam__1___redArg(x_69);
return x_76;
}
else
{
lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_box(0);
x_78 = lean_usize_of_nat(x_39);
x_79 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_80 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_70, x_78, x_79, x_77, x_2, x_69);
lean_dec(x_70);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lake_loadWorkspace___elam__1___redArg(x_81);
return x_82;
}
}
}
}
block_38:
{
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 6);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lake_joinRelative(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lake_Manifest_load_x3f(x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_2, x_9, x_18, x_5, x_8, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(x_2, x_9, x_21, x_5, x_6, x_4, x_20);
lean_dec(x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_io_error_to_string(x_23);
x_26 = lean_box(3);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
x_29 = lean_apply_2(x_2, x_27, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_36 = lean_box(0);
x_37 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_2, x_9, x_36, x_5, x_8, x_10);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_loadWorkspace___elam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lake_Workspace_materializeDeps___at___Lake_loadWorkspace_spec__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_loadWorkspace___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_1, 9);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*12 + 2);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
x_29 = l_Lake_loadWorkspaceRoot(x_1, x_28, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_array_get_size(x_33);
x_35 = lean_nat_dec_lt(x_27, x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
x_13 = x_32;
x_14 = x_31;
goto block_26;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_34, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
x_13 = x_32;
x_14 = x_31;
goto block_26;
}
else
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_box(0);
x_38 = lean_usize_of_nat(x_27);
x_39 = lean_usize_of_nat(x_34);
lean_dec(x_34);
lean_inc(x_3);
x_40 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_33, x_38, x_39, x_37, x_3, x_31);
lean_dec(x_33);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_13 = x_32;
x_14 = x_41;
goto block_26;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_29, 1);
x_44 = lean_ctor_get(x_29, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_array_get_size(x_45);
x_47 = lean_nat_dec_lt(x_27, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_3);
x_48 = lean_box(0);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_48);
return x_29;
}
else
{
uint8_t x_49; 
lean_free_object(x_29);
x_49 = lean_nat_dec_le(x_46, x_46);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_3);
x_50 = l_Lake_loadWorkspace___elam__1___redArg(x_43);
x_5 = x_50;
goto block_10;
}
else
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_box(0);
x_52 = lean_usize_of_nat(x_27);
x_53 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_54 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_45, x_52, x_53, x_51, x_3, x_43);
lean_dec(x_45);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lake_loadWorkspace___elam__1___redArg(x_55);
x_5 = x_56;
goto block_10;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_dec(x_29);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
lean_dec(x_30);
x_59 = lean_array_get_size(x_58);
x_60 = lean_nat_dec_lt(x_27, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_59, x_59);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
x_64 = l_Lake_loadWorkspace___elam__1___redArg(x_57);
x_5 = x_64;
goto block_10;
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_box(0);
x_66 = lean_usize_of_nat(x_27);
x_67 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_68 = l_Array_foldlMUnsafe_fold___at___Lake_loadWorkspace_spec__2(x_58, x_66, x_67, x_65, x_3, x_57);
lean_dec(x_58);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lake_loadWorkspace___elam__1___redArg(x_69);
x_5 = x_70;
goto block_10;
}
}
}
}
block_10:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
block_26:
{
lean_object* x_15; 
x_15 = l_Lake_Workspace_updateAndMaterialize___at___Lake_loadWorkspace_spec__0(x_3, x_13, x_2, x_11, x_12, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_updateManifest(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lake_Load_Resolve(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Workspace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Resolve(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InitFacets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
