// Lean compiler output
// Module: Lake.Build.Target.Fetch
// Imports: Lake.Build.Job Lake.Config.Monad
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
LEAN_EXPORT uint8_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lake_instDataKindModule;
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindPackage;
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Target_fetchIn___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1(uint8_t, lean_object*);
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instMonad(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lake_Job_collectArray(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_PartialBuildKey_moduleTargetIndicator;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Name_isAnonymous(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
lean_inc(x_3);
x_11 = l_Lake_RBNode_dFind___redArg(x_10, x_9, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_box(x_7);
x_13 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_15 = l_Lake_BuildKey_toString(x_2);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("': package '", 12, 12);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Name_toString(x_3, x_20, x_13);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_box(3);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_array_get_size(x_5);
x_29 = lean_array_push(x_5, x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Name_isAnonymous(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
lean_inc(x_3);
x_14 = l_Lake_RBNode_dFind___redArg(x_13, x_12, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_box(x_10);
x_16 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_18 = l_Lake_BuildKey_toString(x_2);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("': package '", 12, 12);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Name_toString(x_3, x_23, x_16);
x_25 = lean_string_append(x_21, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_box(3);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_array_get_size(x_8);
x_32 = lean_array_push(x_8, x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_8);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_3);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_apply_6(x_5, x_11, x_6, x_7, x_8, x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_19);
lean_ctor_set(x_14, 1, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_31 = x_14;
} else {
 lean_dec_ref(x_14);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_32);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_13, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_14, 1);
x_41 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_41);
lean_ctor_set(x_14, 1, x_43);
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_dec(x_9);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_46);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_13, 0, x_49);
return x_13;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_dec(x_13);
x_51 = lean_ctor_get(x_14, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_53 = x_14;
} else {
 lean_dec_ref(x_14);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_54);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_instDataKindModule;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
lean_inc(x_12);
x_14 = l_Lake_Workspace_findModule_x3f(x_12, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 1, 0);
x_16 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_17 = l_Lake_BuildKey_toString(x_2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("': module '", 11, 11);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Name_toString(x_12, x_22, x_15);
x_24 = lean_string_append(x_20, x_23);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_box(3);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_array_get_size(x_9);
x_31 = lean_array_push(x_9, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_2);
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_mk_empty_array_with_capacity(x_35);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = lean_box(0);
x_39 = lean_mk_string_unchecked("<nil>", 5, 5);
x_40 = l_Lake_BuildTrace_nil(x_39);
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_unbox(x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_task_pure(x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_11);
lean_ctor_set(x_46, 2, x_37);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_10);
return x_50;
}
}
case 1:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_76; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_52 = x_3;
} else {
 lean_dec_ref(x_3);
 x_52 = lean_box(0);
}
x_53 = l_Lake_instDataKindPackage;
x_76 = l_Lean_Name_isAnonymous(x_51);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_77 = lean_ctor_get(x_8, 1);
lean_inc(x_77);
lean_dec(x_8);
x_78 = lean_ctor_get(x_77, 4);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_78, x_51);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_52);
x_80 = lean_box(x_76);
x_81 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed), 2, 1);
lean_closure_set(x_81, 0, x_80);
x_82 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_83 = l_Lake_BuildKey_toString(x_2);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = lean_mk_string_unchecked("': package '", 12, 12);
x_86 = lean_string_append(x_84, x_85);
lean_dec(x_85);
x_87 = lean_box(1);
x_88 = lean_unbox(x_87);
x_89 = l_Lean_Name_toString(x_51, x_88, x_81);
x_90 = lean_string_append(x_86, x_89);
lean_dec(x_89);
x_91 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_93 = lean_box(3);
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_unbox(x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_95);
x_96 = lean_array_get_size(x_9);
x_97 = lean_array_push(x_9, x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_10);
return x_99;
}
else
{
lean_object* x_100; 
lean_dec(x_51);
lean_dec(x_2);
x_100 = lean_ctor_get(x_79, 0);
lean_inc(x_100);
lean_dec(x_79);
x_54 = x_100;
x_55 = x_9;
x_56 = x_10;
goto block_75;
}
}
else
{
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_2);
x_54 = x_1;
x_55 = x_9;
x_56 = x_10;
goto block_75;
}
block_75:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_mk_empty_array_with_capacity(x_59);
x_61 = lean_mk_string_unchecked("", 0, 0);
x_62 = lean_box(0);
x_63 = lean_mk_string_unchecked("<nil>", 5, 5);
x_64 = l_Lake_BuildTrace_nil(x_63);
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unbox(x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_66);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_54);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_task_pure(x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_53);
lean_ctor_set(x_70, 2, x_61);
x_71 = lean_unbox(x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_55);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_56);
return x_74;
}
}
case 2:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_298; 
x_101 = lean_ctor_get(x_3, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_3, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_103 = x_3;
} else {
 lean_dec_ref(x_3);
 x_103 = lean_box(0);
}
x_104 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 1, 0);
x_298 = l_Lean_Name_isAnonymous(x_101);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_1);
x_299 = lean_ctor_get(x_8, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_299, 4);
lean_inc(x_300);
lean_dec(x_299);
x_301 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_300, x_101);
lean_dec(x_300);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_302 = lean_box(x_298);
x_303 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed), 2, 1);
lean_closure_set(x_303, 0, x_302);
x_304 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_305 = l_Lake_BuildKey_toString(x_2);
x_306 = lean_string_append(x_304, x_305);
lean_dec(x_305);
x_307 = lean_mk_string_unchecked("': package '", 12, 12);
x_308 = lean_string_append(x_306, x_307);
lean_dec(x_307);
x_309 = lean_box(1);
x_310 = lean_unbox(x_309);
x_311 = l_Lean_Name_toString(x_101, x_310, x_303);
x_312 = lean_string_append(x_308, x_311);
lean_dec(x_311);
x_313 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_314 = lean_string_append(x_312, x_313);
lean_dec(x_313);
x_315 = lean_box(3);
x_316 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_316, 0, x_314);
x_317 = lean_unbox(x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*1, x_317);
x_318 = lean_array_get_size(x_9);
x_319 = lean_array_push(x_9, x_316);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_10);
return x_321;
}
else
{
lean_object* x_322; 
lean_dec(x_101);
x_322 = lean_ctor_get(x_301, 0);
lean_inc(x_322);
lean_dec(x_301);
x_105 = x_322;
x_106 = x_9;
x_107 = x_10;
goto block_297;
}
}
else
{
lean_dec(x_101);
x_105 = x_1;
x_106 = x_9;
x_107 = x_10;
goto block_297;
}
block_297:
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lake_PartialBuildKey_moduleTargetIndicator;
lean_inc(x_102);
x_109 = l_Lean_Name_eraseSuffix_x3f(x_102, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
lean_inc(x_102);
lean_inc(x_110);
if (lean_is_scalar(x_103)) {
 x_111 = lean_alloc_ctor(2, 2, 0);
} else {
 x_111 = x_103;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_102);
if (x_4 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_110);
lean_dec(x_104);
lean_dec(x_2);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_102);
x_113 = lean_apply_6(x_5, x_112, x_6, x_7, x_8, x_106, x_107);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_113);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_113, 0);
lean_dec(x_116);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_111);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_114, 0, x_119);
return x_113;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_114, 0);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_114);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_111);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_113, 0, x_123);
return x_113;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_113, 1);
lean_inc(x_124);
lean_dec(x_113);
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_111);
lean_ctor_set(x_128, 1, x_125);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_124);
return x_130;
}
}
else
{
uint8_t x_131; 
lean_dec(x_111);
x_131 = !lean_is_exclusive(x_113);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_113, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_114);
if (x_133 == 0)
{
return x_113;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_114, 0);
x_135 = lean_ctor_get(x_114, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_114);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_113, 0, x_136);
return x_113;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_113, 1);
lean_inc(x_137);
lean_dec(x_113);
x_138 = lean_ctor_get(x_114, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_114, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_140 = x_114;
} else {
 lean_dec_ref(x_114);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_137);
return x_142;
}
}
}
else
{
lean_object* x_143; 
x_143 = l_Lake_Package_findTargetDecl_x3f(x_102, x_105);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_111);
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_144 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_145 = l_Lake_BuildKey_toString(x_2);
x_146 = lean_string_append(x_144, x_145);
lean_dec(x_145);
x_147 = lean_mk_string_unchecked("': target not found in package '", 32, 32);
x_148 = lean_string_append(x_146, x_147);
lean_dec(x_147);
x_149 = l_Lean_Name_toString(x_110, x_4, x_104);
x_150 = lean_string_append(x_148, x_149);
lean_dec(x_149);
x_151 = lean_mk_string_unchecked("'", 1, 1);
x_152 = lean_string_append(x_150, x_151);
lean_dec(x_151);
x_153 = lean_box(3);
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_152);
x_155 = lean_unbox(x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_155);
x_156 = lean_array_get_size(x_106);
x_157 = lean_array_push(x_106, x_154);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_107);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_110);
lean_dec(x_104);
lean_dec(x_2);
x_160 = lean_ctor_get(x_143, 0);
lean_inc(x_160);
lean_dec(x_143);
x_161 = lean_ctor_get(x_160, 2);
lean_inc(x_161);
x_162 = l_Lean_Name_isAnonymous(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_102);
x_163 = lean_mk_string_unchecked("default", 7, 7);
lean_inc(x_161);
x_164 = l_Lean_Name_str___override(x_161, x_163);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 3);
lean_inc(x_166);
lean_dec(x_160);
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_105);
lean_ctor_set(x_167, 1, x_165);
lean_ctor_set(x_167, 2, x_166);
lean_inc(x_164);
lean_inc(x_111);
x_168 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_168, 0, x_111);
lean_ctor_set(x_168, 1, x_161);
lean_ctor_set(x_168, 2, x_167);
lean_ctor_set(x_168, 3, x_164);
x_169 = lean_apply_6(x_5, x_168, x_6, x_7, x_8, x_106, x_107);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_169);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_169, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_170);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_170, 0);
x_175 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_175, 0, x_111);
lean_ctor_set(x_175, 1, x_164);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_170, 0, x_176);
return x_169;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_170, 0);
x_178 = lean_ctor_get(x_170, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_170);
x_179 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_179, 0, x_111);
lean_ctor_set(x_179, 1, x_164);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_169, 0, x_181);
return x_169;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_182 = lean_ctor_get(x_169, 1);
lean_inc(x_182);
lean_dec(x_169);
x_183 = lean_ctor_get(x_170, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_170, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_185 = x_170;
} else {
 lean_dec_ref(x_170);
 x_185 = lean_box(0);
}
x_186 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_186, 0, x_111);
lean_ctor_set(x_186, 1, x_164);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_183);
if (lean_is_scalar(x_185)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_185;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_182);
return x_189;
}
}
else
{
uint8_t x_190; 
lean_dec(x_164);
lean_dec(x_111);
x_190 = !lean_is_exclusive(x_169);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_169, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_170);
if (x_192 == 0)
{
return x_169;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_170, 0);
x_194 = lean_ctor_get(x_170, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_170);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_169, 0, x_195);
return x_169;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_169, 1);
lean_inc(x_196);
lean_dec(x_169);
x_197 = lean_ctor_get(x_170, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_170, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_199 = x_170;
} else {
 lean_dec_ref(x_170);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_196);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_161);
lean_dec(x_160);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_105);
lean_ctor_set(x_202, 1, x_102);
x_203 = lean_apply_6(x_5, x_202, x_6, x_7, x_8, x_106, x_107);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_203);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_203, 0);
lean_dec(x_206);
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_204, 0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_111);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_204, 0, x_209);
return x_203;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_204, 0);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_204);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_111);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
lean_ctor_set(x_203, 0, x_213);
return x_203;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_203, 1);
lean_inc(x_214);
lean_dec(x_203);
x_215 = lean_ctor_get(x_204, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_204, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_217 = x_204;
} else {
 lean_dec_ref(x_204);
 x_217 = lean_box(0);
}
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_111);
lean_ctor_set(x_218, 1, x_215);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_214);
return x_220;
}
}
else
{
uint8_t x_221; 
lean_dec(x_111);
x_221 = !lean_is_exclusive(x_203);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_203, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_204);
if (x_223 == 0)
{
return x_203;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_204, 0);
x_225 = lean_ctor_get(x_204, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_204);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_203, 0, x_226);
return x_203;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_203, 1);
lean_inc(x_227);
lean_dec(x_203);
x_228 = lean_ctor_get(x_204, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_204, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_230 = x_204;
} else {
 lean_dec_ref(x_204);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_227);
return x_232;
}
}
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_233 = lean_ctor_get(x_109, 0);
lean_inc(x_233);
lean_dec(x_109);
lean_inc(x_105);
lean_inc(x_233);
x_234 = l_Lake_Package_findTargetModule_x3f(x_233, x_105);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_235 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_236 = l_Lake_BuildKey_toString(x_2);
x_237 = lean_string_append(x_235, x_236);
lean_dec(x_236);
x_238 = lean_mk_string_unchecked("': module target '", 18, 18);
x_239 = lean_string_append(x_237, x_238);
lean_dec(x_238);
x_240 = lean_box(1);
x_241 = lean_unbox(x_240);
lean_inc(x_104);
x_242 = l_Lean_Name_toString(x_233, x_241, x_104);
x_243 = lean_string_append(x_239, x_242);
lean_dec(x_242);
x_244 = lean_mk_string_unchecked("' not found in package '", 24, 24);
x_245 = lean_string_append(x_243, x_244);
lean_dec(x_244);
x_246 = lean_ctor_get(x_105, 0);
lean_inc(x_246);
lean_dec(x_105);
x_247 = lean_unbox(x_240);
x_248 = l_Lean_Name_toString(x_246, x_247, x_104);
x_249 = lean_string_append(x_245, x_248);
lean_dec(x_248);
x_250 = lean_mk_string_unchecked("'", 1, 1);
x_251 = lean_string_append(x_249, x_250);
lean_dec(x_250);
x_252 = lean_box(3);
x_253 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_253, 0, x_251);
x_254 = lean_unbox(x_252);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_254);
x_255 = lean_array_get_size(x_106);
x_256 = lean_array_push(x_106, x_253);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_107);
return x_258;
}
else
{
uint8_t x_259; 
lean_dec(x_233);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_2);
x_259 = !lean_is_exclusive(x_234);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_260 = lean_ctor_get(x_234, 0);
x_261 = lean_ctor_get(x_260, 2);
lean_inc(x_261);
lean_ctor_set_tag(x_234, 0);
lean_ctor_set(x_234, 0, x_261);
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_mk_empty_array_with_capacity(x_262);
x_264 = lean_mk_string_unchecked("", 0, 0);
x_265 = lean_box(0);
x_266 = lean_mk_string_unchecked("<nil>", 5, 5);
x_267 = l_Lake_BuildTrace_nil(x_266);
x_268 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_268, 0, x_263);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_unbox(x_265);
lean_ctor_set_uint8(x_268, sizeof(void*)*2, x_269);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_260);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_task_pure(x_270);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_11);
lean_ctor_set(x_273, 2, x_264);
x_274 = lean_unbox(x_272);
lean_ctor_set_uint8(x_273, sizeof(void*)*3, x_274);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_234);
lean_ctor_set(x_275, 1, x_273);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_106);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_107);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_278 = lean_ctor_get(x_234, 0);
lean_inc(x_278);
lean_dec(x_234);
x_279 = lean_ctor_get(x_278, 2);
lean_inc(x_279);
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_281 = lean_unsigned_to_nat(0u);
x_282 = lean_mk_empty_array_with_capacity(x_281);
x_283 = lean_mk_string_unchecked("", 0, 0);
x_284 = lean_box(0);
x_285 = lean_mk_string_unchecked("<nil>", 5, 5);
x_286 = l_Lake_BuildTrace_nil(x_285);
x_287 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_287, 0, x_282);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_unbox(x_284);
lean_ctor_set_uint8(x_287, sizeof(void*)*2, x_288);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_278);
lean_ctor_set(x_289, 1, x_287);
x_290 = lean_task_pure(x_289);
x_291 = lean_box(0);
x_292 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_11);
lean_ctor_set(x_292, 2, x_283);
x_293 = lean_unbox(x_291);
lean_ctor_set_uint8(x_292, sizeof(void*)*3, x_293);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_280);
lean_ctor_set(x_294, 1, x_292);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_106);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_107);
return x_296;
}
}
}
}
}
default: 
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; 
x_323 = lean_ctor_get(x_3, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_3, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_325 = x_3;
} else {
 lean_dec_ref(x_3);
 x_325 = lean_box(0);
}
x_326 = lean_box(0);
x_327 = lean_unbox(x_326);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_323);
lean_inc(x_2);
x_328 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_323, x_327, x_5, x_6, x_7, x_8, x_9, x_10);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_328, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_332 = x_328;
} else {
 lean_dec_ref(x_328);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_329, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_334 = x_329;
} else {
 lean_dec_ref(x_329);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_330, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_336 = x_330;
} else {
 lean_dec_ref(x_330);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
x_338 = l_Lean_Name_isAnonymous(x_337);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_383; 
x_339 = lean_box(x_338);
x_340 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed), 2, 1);
lean_closure_set(x_340, 0, x_339);
x_383 = l_Lean_Name_isAnonymous(x_324);
if (x_383 == 0)
{
x_341 = x_324;
goto block_382;
}
else
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_324);
x_384 = lean_mk_string_unchecked("default", 7, 7);
x_385 = l_Lean_Name_mkStr1(x_384);
x_341 = x_385;
goto block_382;
}
block_382:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_inc(x_337);
x_342 = l_Lean_Name_append(x_337, x_341);
x_343 = lean_ctor_get(x_8, 1);
lean_inc(x_343);
x_344 = l_Lake_Workspace_findFacetConfig_x3f(x_342, x_343);
lean_dec(x_343);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_325);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_345 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_346 = l_Lake_BuildKey_toString(x_2);
x_347 = lean_string_append(x_345, x_346);
lean_dec(x_346);
x_348 = lean_mk_string_unchecked("': unknown facet '", 18, 18);
x_349 = lean_string_append(x_347, x_348);
lean_dec(x_348);
x_350 = lean_box(1);
x_351 = lean_unbox(x_350);
x_352 = l_Lean_Name_toString(x_342, x_351, x_340);
x_353 = lean_string_append(x_349, x_352);
lean_dec(x_352);
x_354 = lean_mk_string_unchecked("'", 1, 1);
x_355 = lean_string_append(x_353, x_354);
lean_dec(x_354);
x_356 = lean_box(3);
x_357 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_357, 0, x_355);
x_358 = lean_unbox(x_356);
lean_ctor_set_uint8(x_357, sizeof(void*)*1, x_358);
x_359 = lean_array_get_size(x_333);
x_360 = lean_array_push(x_333, x_357);
if (lean_is_scalar(x_334)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_334;
 lean_ctor_set_tag(x_361, 1);
}
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
if (lean_is_scalar(x_332)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_332;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_331);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; uint8_t x_371; 
lean_dec(x_340);
lean_dec(x_332);
lean_dec(x_2);
x_363 = lean_ctor_get(x_344, 0);
lean_inc(x_363);
lean_dec(x_344);
lean_inc(x_342);
lean_inc(x_323);
x_364 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__7), 10, 3);
lean_closure_set(x_364, 0, x_323);
lean_closure_set(x_364, 1, x_337);
lean_closure_set(x_364, 2, x_342);
x_365 = lean_ctor_get(x_363, 2);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_unsigned_to_nat(0u);
x_367 = lean_mk_string_unchecked("<nil>", 5, 5);
x_368 = l_Lake_BuildTrace_nil(x_367);
x_369 = lean_unbox(x_326);
x_370 = l_Lake_Job_bindM___redArg(x_365, x_335, x_364, x_366, x_369, x_5, x_6, x_7, x_8, x_368, x_331);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_372 = lean_ctor_get(x_370, 0);
if (lean_is_scalar(x_325)) {
 x_373 = lean_alloc_ctor(3, 2, 0);
} else {
 x_373 = x_325;
}
lean_ctor_set(x_373, 0, x_323);
lean_ctor_set(x_373, 1, x_342);
if (lean_is_scalar(x_336)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_336;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
if (lean_is_scalar(x_334)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_334;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_333);
lean_ctor_set(x_370, 0, x_375);
return x_370;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_370, 0);
x_377 = lean_ctor_get(x_370, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_370);
if (lean_is_scalar(x_325)) {
 x_378 = lean_alloc_ctor(3, 2, 0);
} else {
 x_378 = x_325;
}
lean_ctor_set(x_378, 0, x_323);
lean_ctor_set(x_378, 1, x_342);
if (lean_is_scalar(x_336)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_336;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_376);
if (lean_is_scalar(x_334)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_334;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_333);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_377);
return x_381;
}
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_386 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_387 = l_Lake_BuildKey_toString(x_2);
x_388 = lean_string_append(x_386, x_387);
lean_dec(x_387);
x_389 = lean_mk_string_unchecked("': targets of opaque data kinds do not support facets", 53, 53);
x_390 = lean_string_append(x_388, x_389);
lean_dec(x_389);
x_391 = lean_box(3);
x_392 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_392, 0, x_390);
x_393 = lean_unbox(x_391);
lean_ctor_set_uint8(x_392, sizeof(void*)*1, x_393);
x_394 = lean_array_get_size(x_333);
x_395 = lean_array_push(x_333, x_392);
if (lean_is_scalar(x_334)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_334;
 lean_ctor_set_tag(x_396, 1);
}
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
if (lean_is_scalar(x_332)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_332;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_331);
return x_397;
}
}
else
{
lean_dec(x_329);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_328;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchInCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc(x_2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_fetchIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
lean_inc(x_2);
x_11 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_1, x_2, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lake_Job_toOpaque___redArg(x_17);
lean_dec(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lake_Job_toOpaque___redArg(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_27 = x_12;
} else {
 lean_dec_ref(x_12);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lake_Job_toOpaque___redArg(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_11, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_11, 0, x_37);
return x_11;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_41 = x_12;
} else {
 lean_dec_ref(x_12);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_3);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_apply_6(x_5, x_11, x_6, x_7, x_8, x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_19);
lean_ctor_set(x_14, 1, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_31 = x_14;
} else {
 lean_dec_ref(x_14);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_32);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_31;
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_13, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_14, 1);
x_41 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_41);
lean_ctor_set(x_14, 1, x_43);
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_dec(x_9);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_46);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_13, 0, x_49);
return x_13;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_dec(x_13);
x_51 = lean_ctor_get(x_14, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_53 = x_14;
} else {
 lean_dec_ref(x_14);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_54);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_9);
x_11 = l_Lake_Workspace_findModule_x3f(x_9, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 1, 0);
x_13 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_14 = l_Lake_BuildKey_toString(x_1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("': module '", 11, 11);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Name_toString(x_9, x_19, x_12);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_box(3);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_array_get_size(x_7);
x_28 = lean_array_push(x_7, x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_1);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = l_Lake_instDataKindModule;
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_mk_string_unchecked("", 0, 0);
x_36 = lean_box(0);
x_37 = lean_mk_string_unchecked("<nil>", 5, 5);
x_38 = l_Lake_BuildTrace_nil(x_37);
x_39 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_task_pure(x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_32);
lean_ctor_set(x_44, 2, x_35);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
return x_47;
}
}
case 1:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_dec(x_6);
x_50 = lean_ctor_get(x_49, 4);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_50, x_48);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 1, 0);
x_53 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_54 = l_Lake_BuildKey_toString(x_1);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked("': package '", 12, 12);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = lean_box(1);
x_59 = lean_unbox(x_58);
x_60 = l_Lean_Name_toString(x_48, x_59, x_52);
x_61 = lean_string_append(x_57, x_60);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = lean_box(3);
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_66);
x_67 = lean_array_get_size(x_7);
x_68 = lean_array_push(x_7, x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_48);
lean_dec(x_1);
x_71 = lean_ctor_get(x_51, 0);
lean_inc(x_71);
lean_dec(x_51);
x_72 = l_Lake_instDataKindPackage;
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_mk_empty_array_with_capacity(x_73);
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = lean_box(0);
x_77 = lean_mk_string_unchecked("<nil>", 5, 5);
x_78 = l_Lake_BuildTrace_nil(x_77);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_unbox(x_76);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_task_pure(x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_72);
lean_ctor_set(x_84, 2, x_75);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_7);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_8);
return x_87;
}
}
case 2:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_ctor_get(x_2, 1);
x_91 = lean_ctor_get(x_6, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 4);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_92, x_89);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_90);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 1, 0);
x_95 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_96 = l_Lake_BuildKey_toString(x_1);
x_97 = lean_string_append(x_95, x_96);
lean_dec(x_96);
x_98 = lean_mk_string_unchecked("': package '", 12, 12);
x_99 = lean_string_append(x_97, x_98);
lean_dec(x_98);
x_100 = lean_box(1);
x_101 = lean_unbox(x_100);
x_102 = l_Lean_Name_toString(x_89, x_101, x_94);
x_103 = lean_string_append(x_99, x_102);
lean_dec(x_102);
x_104 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_105 = lean_string_append(x_103, x_104);
lean_dec(x_104);
x_106 = lean_box(3);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
x_109 = lean_array_get_size(x_7);
x_110 = lean_array_push(x_7, x_107);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_110);
lean_ctor_set(x_2, 0, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_8);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_89);
lean_dec(x_1);
x_112 = lean_ctor_get(x_93, 0);
lean_inc(x_112);
lean_dec(x_93);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_112);
x_113 = lean_apply_6(x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_2, 0);
x_115 = lean_ctor_get(x_2, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_2);
x_116 = lean_ctor_get(x_6, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 4);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_117, x_114);
lean_dec(x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_115);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed), 1, 0);
x_120 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_121 = l_Lake_BuildKey_toString(x_1);
x_122 = lean_string_append(x_120, x_121);
lean_dec(x_121);
x_123 = lean_mk_string_unchecked("': package '", 12, 12);
x_124 = lean_string_append(x_122, x_123);
lean_dec(x_123);
x_125 = lean_box(1);
x_126 = lean_unbox(x_125);
x_127 = l_Lean_Name_toString(x_114, x_126, x_119);
x_128 = lean_string_append(x_124, x_127);
lean_dec(x_127);
x_129 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
x_130 = lean_string_append(x_128, x_129);
lean_dec(x_129);
x_131 = lean_box(3);
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_unbox(x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_133);
x_134 = lean_array_get_size(x_7);
x_135 = lean_array_push(x_7, x_132);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_8);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_114);
lean_dec(x_1);
x_138 = lean_ctor_get(x_118, 0);
lean_inc(x_138);
lean_dec(x_118);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_115);
x_140 = lean_apply_6(x_3, x_139, x_4, x_5, x_6, x_7, x_8);
return x_140;
}
}
}
default: 
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_2, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 1);
lean_inc(x_142);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_141);
lean_inc(x_1);
x_143 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_1, x_141, x_3, x_4, x_5, x_6, x_7, x_8);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_143, 1);
x_147 = lean_ctor_get(x_143, 0);
lean_dec(x_147);
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_144, 0);
x_150 = lean_ctor_get(x_144, 1);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
x_152 = l_Lean_Name_isAnonymous(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_2);
x_153 = lean_ctor_get(x_6, 1);
lean_inc(x_153);
x_154 = l_Lake_Workspace_findFacetConfig_x3f(x_142, x_153);
lean_dec(x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_155 = lean_box(x_152);
x_156 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed), 2, 1);
lean_closure_set(x_156, 0, x_155);
x_157 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_158 = l_Lake_BuildKey_toString(x_1);
x_159 = lean_string_append(x_157, x_158);
lean_dec(x_158);
x_160 = lean_mk_string_unchecked("': unknown facet '", 18, 18);
x_161 = lean_string_append(x_159, x_160);
lean_dec(x_160);
x_162 = lean_box(1);
x_163 = lean_unbox(x_162);
x_164 = l_Lean_Name_toString(x_142, x_163, x_156);
x_165 = lean_string_append(x_161, x_164);
lean_dec(x_164);
x_166 = lean_mk_string_unchecked("'", 1, 1);
x_167 = lean_string_append(x_165, x_166);
lean_dec(x_166);
x_168 = lean_box(3);
x_169 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_unbox(x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_170);
x_171 = lean_array_get_size(x_150);
x_172 = lean_array_push(x_150, x_169);
lean_ctor_set_tag(x_144, 1);
lean_ctor_set(x_144, 1, x_172);
lean_ctor_set(x_144, 0, x_171);
return x_143;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_free_object(x_143);
lean_dec(x_1);
x_173 = lean_ctor_get(x_154, 0);
lean_inc(x_173);
lean_dec(x_154);
x_174 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__4), 10, 3);
lean_closure_set(x_174, 0, x_141);
lean_closure_set(x_174, 1, x_151);
lean_closure_set(x_174, 2, x_142);
x_175 = lean_ctor_get(x_173, 2);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_mk_string_unchecked("<nil>", 5, 5);
x_178 = l_Lake_BuildTrace_nil(x_177);
x_179 = l_Lake_Job_bindM___redArg(x_175, x_149, x_174, x_176, x_152, x_3, x_4, x_5, x_6, x_178, x_146);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_179, 0);
lean_ctor_set(x_144, 0, x_181);
lean_ctor_set(x_179, 0, x_144);
return x_179;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_179, 0);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_179);
lean_ctor_set(x_144, 0, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_144);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_185 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_186 = l_Lake_BuildKey_toString(x_2);
x_187 = lean_string_append(x_185, x_186);
lean_dec(x_186);
x_188 = lean_mk_string_unchecked("': targets of opaque data kinds do not support facets", 53, 53);
x_189 = lean_string_append(x_187, x_188);
lean_dec(x_188);
x_190 = lean_box(3);
x_191 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_191, 0, x_189);
x_192 = lean_unbox(x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*1, x_192);
x_193 = lean_array_get_size(x_150);
x_194 = lean_array_push(x_150, x_191);
lean_ctor_set_tag(x_144, 1);
lean_ctor_set(x_144, 1, x_194);
lean_ctor_set(x_144, 0, x_193);
return x_143;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = lean_ctor_get(x_144, 0);
x_196 = lean_ctor_get(x_144, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_144);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
x_198 = l_Lean_Name_isAnonymous(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_2);
x_199 = lean_ctor_get(x_6, 1);
lean_inc(x_199);
x_200 = l_Lake_Workspace_findFacetConfig_x3f(x_142, x_199);
lean_dec(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_201 = lean_box(x_198);
x_202 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed), 2, 1);
lean_closure_set(x_202, 0, x_201);
x_203 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_204 = l_Lake_BuildKey_toString(x_1);
x_205 = lean_string_append(x_203, x_204);
lean_dec(x_204);
x_206 = lean_mk_string_unchecked("': unknown facet '", 18, 18);
x_207 = lean_string_append(x_205, x_206);
lean_dec(x_206);
x_208 = lean_box(1);
x_209 = lean_unbox(x_208);
x_210 = l_Lean_Name_toString(x_142, x_209, x_202);
x_211 = lean_string_append(x_207, x_210);
lean_dec(x_210);
x_212 = lean_mk_string_unchecked("'", 1, 1);
x_213 = lean_string_append(x_211, x_212);
lean_dec(x_212);
x_214 = lean_box(3);
x_215 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_215, 0, x_213);
x_216 = lean_unbox(x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_216);
x_217 = lean_array_get_size(x_196);
x_218 = lean_array_push(x_196, x_215);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_143, 0, x_219);
return x_143;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_free_object(x_143);
lean_dec(x_1);
x_220 = lean_ctor_get(x_200, 0);
lean_inc(x_220);
lean_dec(x_200);
x_221 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__4), 10, 3);
lean_closure_set(x_221, 0, x_141);
lean_closure_set(x_221, 1, x_197);
lean_closure_set(x_221, 2, x_142);
x_222 = lean_ctor_get(x_220, 2);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_mk_string_unchecked("<nil>", 5, 5);
x_225 = l_Lake_BuildTrace_nil(x_224);
x_226 = l_Lake_Job_bindM___redArg(x_222, x_195, x_221, x_223, x_198, x_3, x_4, x_5, x_6, x_225, x_146);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_196);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_232 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_233 = l_Lake_BuildKey_toString(x_2);
x_234 = lean_string_append(x_232, x_233);
lean_dec(x_233);
x_235 = lean_mk_string_unchecked("': targets of opaque data kinds do not support facets", 53, 53);
x_236 = lean_string_append(x_234, x_235);
lean_dec(x_235);
x_237 = lean_box(3);
x_238 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_238, 0, x_236);
x_239 = lean_unbox(x_237);
lean_ctor_set_uint8(x_238, sizeof(void*)*1, x_239);
x_240 = lean_array_get_size(x_196);
x_241 = lean_array_push(x_196, x_238);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
lean_ctor_set(x_143, 0, x_242);
return x_143;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_243 = lean_ctor_get(x_143, 1);
lean_inc(x_243);
lean_dec(x_143);
x_244 = lean_ctor_get(x_144, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_144, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_246 = x_144;
} else {
 lean_dec_ref(x_144);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
x_248 = l_Lean_Name_isAnonymous(x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_2);
x_249 = lean_ctor_get(x_6, 1);
lean_inc(x_249);
x_250 = l_Lake_Workspace_findFacetConfig_x3f(x_142, x_249);
lean_dec(x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_247);
lean_dec(x_244);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_251 = lean_box(x_248);
x_252 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__1___boxed), 2, 1);
lean_closure_set(x_252, 0, x_251);
x_253 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_254 = l_Lake_BuildKey_toString(x_1);
x_255 = lean_string_append(x_253, x_254);
lean_dec(x_254);
x_256 = lean_mk_string_unchecked("': unknown facet '", 18, 18);
x_257 = lean_string_append(x_255, x_256);
lean_dec(x_256);
x_258 = lean_box(1);
x_259 = lean_unbox(x_258);
x_260 = l_Lean_Name_toString(x_142, x_259, x_252);
x_261 = lean_string_append(x_257, x_260);
lean_dec(x_260);
x_262 = lean_mk_string_unchecked("'", 1, 1);
x_263 = lean_string_append(x_261, x_262);
lean_dec(x_262);
x_264 = lean_box(3);
x_265 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_265, 0, x_263);
x_266 = lean_unbox(x_264);
lean_ctor_set_uint8(x_265, sizeof(void*)*1, x_266);
x_267 = lean_array_get_size(x_245);
x_268 = lean_array_push(x_245, x_265);
if (lean_is_scalar(x_246)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_246;
 lean_ctor_set_tag(x_269, 1);
}
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_243);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_1);
x_271 = lean_ctor_get(x_250, 0);
lean_inc(x_271);
lean_dec(x_250);
x_272 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__4), 10, 3);
lean_closure_set(x_272, 0, x_141);
lean_closure_set(x_272, 1, x_247);
lean_closure_set(x_272, 2, x_142);
x_273 = lean_ctor_get(x_271, 2);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_unsigned_to_nat(0u);
x_275 = lean_mk_string_unchecked("<nil>", 5, 5);
x_276 = l_Lake_BuildTrace_nil(x_275);
x_277 = l_Lake_Job_bindM___redArg(x_273, x_244, x_272, x_274, x_248, x_3, x_4, x_5, x_6, x_276, x_243);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_280 = x_277;
} else {
 lean_dec_ref(x_277);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_246;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_245);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_279);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_247);
lean_dec(x_244);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_283 = lean_mk_string_unchecked("invalid target '", 16, 16);
x_284 = l_Lake_BuildKey_toString(x_2);
x_285 = lean_string_append(x_283, x_284);
lean_dec(x_284);
x_286 = lean_mk_string_unchecked("': targets of opaque data kinds do not support facets", 53, 53);
x_287 = lean_string_append(x_285, x_286);
lean_dec(x_286);
x_288 = lean_box(3);
x_289 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_289, 0, x_287);
x_290 = lean_unbox(x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*1, x_290);
x_291 = lean_array_get_size(x_245);
x_292 = lean_array_push(x_245, x_289);
if (lean_is_scalar(x_246)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_246;
 lean_ctor_set_tag(x_293, 1);
}
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_243);
return x_294;
}
}
}
else
{
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_143;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(x_2, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lake_Target_fetchIn___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
lean_inc_n(x_3, 2);
x_12 = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(x_2, x_3, x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_16 = x_12;
} else {
 lean_dec_ref(x_12);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_18 = x_13;
} else {
 lean_dec_ref(x_13);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_name_eq(x_20, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_43; 
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lake_Target_fetchIn___redArg___lam__0___boxed), 1, 0);
x_43 = l_Lean_Name_isAnonymous(x_20);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_box(x_43);
x_45 = lean_alloc_closure((void*)(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_mk_string_unchecked("'", 1, 1);
x_47 = lean_unbox(x_10);
x_48 = l_Lean_Name_toString(x_20, x_47, x_45);
lean_inc(x_46);
x_49 = lean_string_append(x_46, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_46);
lean_dec(x_46);
x_23 = x_50;
goto block_42;
}
else
{
lean_object* x_51; 
lean_dec(x_20);
x_51 = lean_mk_string_unchecked("unknown", 7, 7);
x_23 = x_51;
goto block_42;
}
block_42:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_mk_string_unchecked("type mismtach in target '", 25, 25);
x_25 = l_Lake_PartialBuildKey_toString(x_3);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_mk_string_unchecked("': expected '", 13, 13);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_unbox(x_10);
x_30 = l_Lean_Name_toString(x_1, x_29, x_22);
x_31 = lean_string_append(x_28, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("', got ", 7, 7);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_33, x_23);
lean_dec(x_23);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_array_get_size(x_17);
x_39 = lean_array_push(x_17, x_36);
if (lean_is_scalar(x_18)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_18;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_16)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_16;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_15);
return x_41;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_18)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_18;
}
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_17);
if (lean_is_scalar(x_16)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_16;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_15);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_12, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
return x_12;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_12, 0, x_59);
return x_12;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_ctor_get(x_13, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_63 = x_13;
} else {
 lean_dec_ref(x_13);
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
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_Target_fetchIn___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Target_fetchIn___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Target_fetchIn___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_11 = lean_alloc_closure((void*)(l_Lake_TargetArray_fetchIn___redArg___lam__0), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = l_instMonadEIO(lean_box(0));
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_13, 0, x_12);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 8, 3);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lake_EStateT_instFunctor___redArg(x_16);
x_19 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, lean_box(0));
lean_inc(x_13);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_13);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
x_24 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_23);
x_25 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_24);
x_26 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_25);
x_27 = l_Lake_EquipT_instMonad(lean_box(0), lean_box(0), x_26);
x_28 = lean_array_size(x_3);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_usize_of_nat(x_29);
x_31 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_27, x_11, x_28, x_30, x_3);
x_32 = lean_apply_6(x_31, x_5, x_6, x_7, x_8, x_9, x_10);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = l_Lake_Job_collectArray(lean_box(0), x_37, x_4);
lean_dec(x_37);
lean_ctor_set(x_33, 0, x_38);
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = l_Lake_Job_collectArray(lean_box(0), x_39, x_4);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_32, 0, x_42);
return x_32;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_46 = x_33;
} else {
 lean_dec_ref(x_33);
 x_46 = lean_box(0);
}
x_47 = l_Lake_Job_collectArray(lean_box(0), x_44, x_4);
lean_dec(x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_32, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_33);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_33, 0);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_33);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_32, 0, x_55);
return x_32;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_32, 1);
lean_inc(x_56);
lean_dec(x_32);
x_57 = lean_ctor_get(x_33, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_59 = x_33;
} else {
 lean_dec_ref(x_33);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetchIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_TargetArray_fetchIn___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* initialize_Lake_Build_Job(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
