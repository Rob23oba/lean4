// Lean compiler output
// Module: Lean.Meta.GeneralizeVars
// Imports: Lean.Meta.Basic Lean.Util.CollectFVars
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
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at___Lean_Meta_getFVarsToGeneralize_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_sortFVarIds___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(uint8_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(x_6, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_14, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_7);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_15);
lean_ctor_set(x_9, 0, x_7);
x_17 = l_Lean_FVarIdSet_insert(x_14, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_1 = x_8;
x_2 = x_18;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_free_object(x_9);
lean_dec(x_7);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 0, x_14);
x_1 = x_8;
x_2 = x_20;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
x_1 = x_8;
x_2 = x_25;
x_3 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_30, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_FVarIdSet_insert(x_30, x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_1 = x_8;
x_2 = x_35;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_38 = x_37;
} else {
 lean_dec_ref(x_37);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
x_1 = x_8;
x_2 = x_39;
x_3 = x_28;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_33; 
lean_inc(x_4);
x_33 = l_Lean_FVarId_getDecl___redArg(x_1, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_83; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_83 = lean_ctor_get(x_34, 3);
lean_inc(x_83);
x_36 = x_83;
goto block_82;
block_82:
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_36, x_5, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_unsigned_to_nat(8u);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_shiftl(x_41, x_43);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_div(x_44, x_45);
lean_dec(x_44);
x_47 = l_Nat_nextPowerOfTwo(x_46);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = lean_mk_array(x_47, x_48);
lean_ctor_set(x_37, 1, x_49);
lean_ctor_set(x_37, 0, x_42);
x_50 = lean_box(0);
x_51 = lean_mk_empty_array_with_capacity(x_42);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_CollectFVars_main(x_39, x_52);
x_54 = l_Lean_LocalDecl_value_x3f(x_34);
lean_dec(x_34);
if (lean_obj_tag(x_54) == 0)
{
x_20 = x_53;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_40;
goto block_32;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_55, x_5, x_40);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_CollectFVars_main(x_57, x_53);
x_20 = x_59;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_58;
goto block_32;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_37, 0);
x_61 = lean_ctor_get(x_37, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_37);
x_62 = lean_unsigned_to_nat(8u);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_nat_shiftl(x_62, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = l_Nat_nextPowerOfTwo(x_67);
lean_dec(x_67);
x_69 = lean_box(0);
x_70 = lean_mk_array(x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_box(0);
x_73 = lean_mk_empty_array_with_capacity(x_63);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_Lean_CollectFVars_main(x_60, x_74);
x_76 = l_Lean_LocalDecl_value_x3f(x_34);
lean_dec(x_34);
if (lean_obj_tag(x_76) == 0)
{
x_20 = x_75;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_61;
goto block_32;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_77, x_5, x_61);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_CollectFVars_main(x_79, x_75);
x_20 = x_81;
x_21 = x_4;
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_80;
goto block_32;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_33);
if (x_84 == 0)
{
return x_33;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_33, 0);
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_33);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
block_19:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_9, 1, x_12);
lean_ctor_set(x_9, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
block_32:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_2);
x_28 = l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(x_26, x_27, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_9 = x_31;
x_10 = x_30;
goto block_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_RBNode_forIn_visit___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_9);
x_12 = l_Lean_FVarIdSet_insert(x_2, x_9);
lean_inc(x_3);
x_13 = l_Lean_Meta_mkGeneralizationForbiddenSet_visit(x_9, x_10, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_16;
x_2 = x_17;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
x_1 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_Expr_isFVar(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = lean_infer_type(x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_24, x_6, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_CollectFVars_main(x_28, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 0, x_30);
x_10 = x_26;
x_11 = x_29;
goto block_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_CollectFVars_main(x_31, x_20);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_21);
x_10 = x_34;
x_11 = x_32;
goto block_16;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Expr_fvarId_x21(x_19);
lean_dec(x_19);
x_40 = lean_array_push(x_21, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_40);
x_10 = x_41;
x_11 = x_9;
goto block_16;
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_Lean_Expr_isFVar(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = lean_infer_type(x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_24, x_6, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_CollectFVars_main(x_28, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 0, x_30);
x_10 = x_26;
x_11 = x_29;
goto block_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_CollectFVars_main(x_31, x_20);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_21);
x_10 = x_34;
x_11 = x_32;
goto block_16;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Expr_fvarId_x21(x_19);
lean_dec(x_19);
x_40 = lean_array_push(x_21, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_40);
x_10 = x_41;
x_11 = x_9;
goto block_16;
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(x_1, x_2, x_14, x_10, x_5, x_6, x_7, x_8, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_8 = lean_unsigned_to_nat(8u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_shiftl(x_8, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_nextPowerOfTwo(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_size(x_1);
x_22 = lean_usize_of_nat(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_21, x_22, x_20, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_array_to_list(x_27);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_mkGeneralizationForbiddenSet_loop(x_28, x_29, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkGeneralizationForbiddenSet_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
lean_inc(x_16);
x_17 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_3, x_15, x_16, x_8, x_9, x_10, x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_add(x_6, x_32);
x_6 = x_33;
x_7 = x_30;
x_12 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; 
x_11 = lean_box(0);
x_20 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_12 = x_21;
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_104; uint8_t x_105; lean_object* x_189; uint8_t x_190; lean_object* x_193; lean_object* x_204; 
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_204 = lean_ctor_get(x_23, 1);
lean_inc(x_204);
x_193 = x_204;
goto block_203;
block_27:
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_12 = x_26;
x_13 = x_8;
goto block_19;
}
block_35:
{
if (x_29 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
x_12 = x_31;
x_13 = x_30;
goto block_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_28);
x_32 = l_Lean_FVarIdSet_insert(x_24, x_28);
x_33 = l_Lean_FVarIdSet_insert(x_25, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_12 = x_34;
x_13 = x_30;
goto block_19;
}
}
block_50:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_st_ref_take(x_7, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_st_ref_set(x_7, x_47, x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_28 = x_36;
x_29 = x_38;
x_30 = x_49;
goto block_35;
}
block_58:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unbox(x_55);
lean_dec(x_55);
x_36 = x_51;
x_37 = x_52;
x_38 = x_57;
x_39 = x_56;
goto block_50;
}
block_74:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_take(x_7, x_60);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 4);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
x_72 = lean_st_ref_set(x_7, x_71, x_66);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_28 = x_59;
x_29 = x_61;
x_30 = x_73;
goto block_35;
}
block_81:
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_59 = x_75;
x_60 = x_76;
x_61 = x_80;
x_62 = x_79;
goto block_74;
}
block_93:
{
if (x_87 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasFVar(x_86);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Expr_hasMVar(x_86);
if (x_90 == 0)
{
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_82);
x_59 = x_83;
x_60 = x_85;
x_61 = x_90;
x_62 = x_88;
goto block_74;
}
else
{
lean_object* x_91; 
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_82, x_84, x_86, x_88);
x_75 = x_83;
x_76 = x_85;
x_77 = x_91;
goto block_81;
}
}
else
{
lean_object* x_92; 
x_92 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_82, x_84, x_86, x_88);
x_75 = x_83;
x_76 = x_85;
x_77 = x_92;
goto block_81;
}
}
else
{
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_82);
x_59 = x_83;
x_60 = x_85;
x_61 = x_87;
x_62 = x_88;
goto block_74;
}
}
block_103:
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_unbox(x_100);
lean_dec(x_100);
x_82 = x_94;
x_83 = x_95;
x_84 = x_96;
x_85 = x_97;
x_86 = x_98;
x_87 = x_102;
x_88 = x_101;
goto block_93;
}
block_188:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_box(x_105);
x_107 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_107, 0, x_106);
x_108 = lean_box(x_105);
x_109 = lean_box(x_9);
lean_inc(x_25);
x_110 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_110, 0, x_25);
lean_closure_set(x_110, 1, x_108);
lean_closure_set(x_110, 2, x_109);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_23, 3);
lean_inc(x_111);
lean_dec(x_23);
x_112 = lean_st_ref_get(x_7, x_8);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_unsigned_to_nat(8u);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_unsigned_to_nat(2u);
x_120 = lean_nat_shiftl(x_117, x_119);
x_121 = lean_unsigned_to_nat(3u);
x_122 = lean_nat_div(x_120, x_121);
lean_dec(x_120);
x_123 = l_Nat_nextPowerOfTwo(x_122);
lean_dec(x_122);
x_124 = lean_box(0);
x_125 = lean_mk_array(x_123, x_124);
lean_ctor_set(x_112, 1, x_125);
lean_ctor_set(x_112, 0, x_118);
lean_inc(x_116);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_116);
x_127 = l_Lean_Expr_hasFVar(x_111);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_hasMVar(x_111);
if (x_128 == 0)
{
lean_dec(x_126);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_107);
x_36 = x_104;
x_37 = x_115;
x_38 = x_128;
x_39 = x_116;
goto block_50;
}
else
{
lean_object* x_129; 
lean_dec(x_116);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_126);
x_51 = x_104;
x_52 = x_115;
x_53 = x_129;
goto block_58;
}
}
else
{
lean_object* x_130; 
lean_dec(x_116);
x_130 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_126);
x_51 = x_104;
x_52 = x_115;
x_53 = x_130;
goto block_58;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_131 = lean_ctor_get(x_112, 0);
x_132 = lean_ctor_get(x_112, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_112);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_unsigned_to_nat(8u);
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_unsigned_to_nat(2u);
x_137 = lean_nat_shiftl(x_134, x_136);
x_138 = lean_unsigned_to_nat(3u);
x_139 = lean_nat_div(x_137, x_138);
lean_dec(x_137);
x_140 = l_Nat_nextPowerOfTwo(x_139);
lean_dec(x_139);
x_141 = lean_box(0);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_142);
lean_inc(x_133);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_133);
x_145 = l_Lean_Expr_hasFVar(x_111);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_111);
if (x_146 == 0)
{
lean_dec(x_144);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_107);
x_36 = x_104;
x_37 = x_132;
x_38 = x_146;
x_39 = x_133;
goto block_50;
}
else
{
lean_object* x_147; 
lean_dec(x_133);
x_147 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_144);
x_51 = x_104;
x_52 = x_132;
x_53 = x_147;
goto block_58;
}
}
else
{
lean_object* x_148; 
lean_dec(x_133);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_144);
x_51 = x_104;
x_52 = x_132;
x_53 = x_148;
goto block_58;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_23, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_23, 4);
lean_inc(x_150);
lean_dec(x_23);
x_151 = lean_st_ref_get(x_7, x_8);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_151, 1);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_unsigned_to_nat(8u);
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_nat_shiftl(x_156, x_158);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_div(x_159, x_160);
lean_dec(x_159);
x_162 = l_Nat_nextPowerOfTwo(x_161);
lean_dec(x_161);
x_163 = lean_box(0);
x_164 = lean_mk_array(x_162, x_163);
lean_ctor_set(x_151, 1, x_164);
lean_ctor_set(x_151, 0, x_157);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_151);
lean_ctor_set(x_165, 1, x_155);
x_166 = l_Lean_Expr_hasFVar(x_149);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = l_Lean_Expr_hasMVar(x_149);
if (x_167 == 0)
{
lean_dec(x_149);
x_82 = x_110;
x_83 = x_104;
x_84 = x_107;
x_85 = x_154;
x_86 = x_150;
x_87 = x_167;
x_88 = x_165;
goto block_93;
}
else
{
lean_object* x_168; 
lean_inc(x_107);
lean_inc(x_110);
x_168 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_165);
x_94 = x_110;
x_95 = x_104;
x_96 = x_107;
x_97 = x_154;
x_98 = x_150;
x_99 = x_168;
goto block_103;
}
}
else
{
lean_object* x_169; 
lean_inc(x_107);
lean_inc(x_110);
x_169 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_165);
x_94 = x_110;
x_95 = x_104;
x_96 = x_107;
x_97 = x_154;
x_98 = x_150;
x_99 = x_169;
goto block_103;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_170 = lean_ctor_get(x_151, 0);
x_171 = lean_ctor_get(x_151, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_151);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_unsigned_to_nat(8u);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_unsigned_to_nat(2u);
x_176 = lean_nat_shiftl(x_173, x_175);
x_177 = lean_unsigned_to_nat(3u);
x_178 = lean_nat_div(x_176, x_177);
lean_dec(x_176);
x_179 = l_Nat_nextPowerOfTwo(x_178);
lean_dec(x_178);
x_180 = lean_box(0);
x_181 = lean_mk_array(x_179, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_174);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_172);
x_184 = l_Lean_Expr_hasFVar(x_149);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = l_Lean_Expr_hasMVar(x_149);
if (x_185 == 0)
{
lean_dec(x_149);
x_82 = x_110;
x_83 = x_104;
x_84 = x_107;
x_85 = x_171;
x_86 = x_150;
x_87 = x_185;
x_88 = x_183;
goto block_93;
}
else
{
lean_object* x_186; 
lean_inc(x_107);
lean_inc(x_110);
x_186 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_183);
x_94 = x_110;
x_95 = x_104;
x_96 = x_107;
x_97 = x_171;
x_98 = x_150;
x_99 = x_186;
goto block_103;
}
}
else
{
lean_object* x_187; 
lean_inc(x_107);
lean_inc(x_110);
x_187 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_183);
x_94 = x_110;
x_95 = x_104;
x_96 = x_107;
x_97 = x_171;
x_98 = x_150;
x_99 = x_187;
goto block_103;
}
}
}
}
block_192:
{
if (x_190 == 0)
{
if (x_2 == 0)
{
x_104 = x_189;
x_105 = x_2;
goto block_188;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_23);
if (x_191 == 0)
{
x_104 = x_189;
x_105 = x_191;
goto block_188;
}
else
{
lean_dec(x_189);
lean_dec(x_23);
goto block_27;
}
}
}
else
{
lean_dec(x_189);
lean_dec(x_23);
goto block_27;
}
}
block_203:
{
lean_object* x_194; 
x_194 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_193);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = l_Lean_LocalDecl_isAuxDecl(x_23);
if (x_195 == 0)
{
uint8_t x_196; uint8_t x_197; 
x_196 = l_Lean_LocalDecl_binderInfo(x_23);
x_197 = l_Lean_BinderInfo_isInstImplicit(x_196);
x_189 = x_193;
x_190 = x_197;
goto block_192;
}
else
{
x_189 = x_193;
x_190 = x_195;
goto block_192;
}
}
else
{
lean_object* x_198; uint8_t x_199; 
lean_dec(x_193);
lean_dec(x_23);
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
lean_dec(x_194);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_198, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_198, 0);
lean_dec(x_201);
lean_ctor_set(x_198, 1, x_25);
lean_ctor_set(x_198, 0, x_24);
x_12 = x_198;
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_202; 
lean_dec(x_198);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_24);
lean_ctor_set(x_202, 1, x_25);
x_12 = x_202;
x_13 = x_8;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_14;
x_8 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_107; uint8_t x_108; lean_object* x_192; uint8_t x_193; lean_object* x_196; lean_object* x_207; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_207 = lean_ctor_get(x_26, 1);
lean_inc(x_207);
x_196 = x_207;
goto block_206;
block_30:
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_15 = x_29;
x_16 = x_11;
goto block_22;
}
block_38:
{
if (x_32 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
x_15 = x_34;
x_16 = x_33;
goto block_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_31);
x_35 = l_Lean_FVarIdSet_insert(x_27, x_31);
x_36 = l_Lean_FVarIdSet_insert(x_28, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_15 = x_37;
x_16 = x_33;
goto block_22;
}
}
block_53:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_st_ref_take(x_8, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 4);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_st_ref_set(x_8, x_50, x_45);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_31 = x_40;
x_32 = x_41;
x_33 = x_52;
goto block_38;
}
block_61:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_39 = x_54;
x_40 = x_55;
x_41 = x_60;
x_42 = x_59;
goto block_53;
}
block_77:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_take(x_8, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 4);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
x_75 = lean_st_ref_set(x_8, x_74, x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_31 = x_62;
x_32 = x_64;
x_33 = x_76;
goto block_38;
}
block_84:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_62 = x_78;
x_63 = x_79;
x_64 = x_83;
x_65 = x_82;
goto block_77;
}
block_96:
{
if (x_90 == 0)
{
uint8_t x_92; 
x_92 = l_Lean_Expr_hasFVar(x_87);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l_Lean_Expr_hasMVar(x_87);
if (x_93 == 0)
{
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_86);
x_62 = x_85;
x_63 = x_88;
x_64 = x_93;
x_65 = x_91;
goto block_77;
}
else
{
lean_object* x_94; 
x_94 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_86, x_89, x_87, x_91);
x_78 = x_85;
x_79 = x_88;
x_80 = x_94;
goto block_84;
}
}
else
{
lean_object* x_95; 
x_95 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_86, x_89, x_87, x_91);
x_78 = x_85;
x_79 = x_88;
x_80 = x_95;
goto block_84;
}
}
else
{
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_86);
x_62 = x_85;
x_63 = x_88;
x_64 = x_90;
x_65 = x_91;
goto block_77;
}
}
block_106:
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox(x_103);
lean_dec(x_103);
x_85 = x_97;
x_86 = x_98;
x_87 = x_99;
x_88 = x_100;
x_89 = x_101;
x_90 = x_105;
x_91 = x_104;
goto block_96;
}
block_191:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_box(x_108);
x_110 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = lean_box(x_108);
x_112 = lean_box(x_12);
lean_inc(x_28);
x_113 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_113, 0, x_28);
lean_closure_set(x_113, 1, x_111);
lean_closure_set(x_113, 2, x_112);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_26, 3);
lean_inc(x_114);
lean_dec(x_26);
x_115 = lean_st_ref_get(x_8, x_11);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_unsigned_to_nat(8u);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_shiftl(x_120, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = l_Nat_nextPowerOfTwo(x_125);
lean_dec(x_125);
x_127 = lean_box(0);
x_128 = lean_mk_array(x_126, x_127);
lean_ctor_set(x_115, 1, x_128);
lean_ctor_set(x_115, 0, x_121);
lean_inc(x_119);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_115);
lean_ctor_set(x_129, 1, x_119);
x_130 = l_Lean_Expr_hasFVar(x_114);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = l_Lean_Expr_hasMVar(x_114);
if (x_131 == 0)
{
lean_dec(x_129);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_110);
x_39 = x_118;
x_40 = x_107;
x_41 = x_131;
x_42 = x_119;
goto block_53;
}
else
{
lean_object* x_132; 
lean_dec(x_119);
x_132 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_129);
x_54 = x_118;
x_55 = x_107;
x_56 = x_132;
goto block_61;
}
}
else
{
lean_object* x_133; 
lean_dec(x_119);
x_133 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_129);
x_54 = x_118;
x_55 = x_107;
x_56 = x_133;
goto block_61;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_134 = lean_ctor_get(x_115, 0);
x_135 = lean_ctor_get(x_115, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_115);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_unsigned_to_nat(8u);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_shiftl(x_137, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = l_Nat_nextPowerOfTwo(x_142);
lean_dec(x_142);
x_144 = lean_box(0);
x_145 = lean_mk_array(x_143, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_138);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_136);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_136);
x_148 = l_Lean_Expr_hasFVar(x_114);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = l_Lean_Expr_hasMVar(x_114);
if (x_149 == 0)
{
lean_dec(x_147);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_110);
x_39 = x_135;
x_40 = x_107;
x_41 = x_149;
x_42 = x_136;
goto block_53;
}
else
{
lean_object* x_150; 
lean_dec(x_136);
x_150 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_147);
x_54 = x_135;
x_55 = x_107;
x_56 = x_150;
goto block_61;
}
}
else
{
lean_object* x_151; 
lean_dec(x_136);
x_151 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_147);
x_54 = x_135;
x_55 = x_107;
x_56 = x_151;
goto block_61;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_26, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_26, 4);
lean_inc(x_153);
lean_dec(x_26);
x_154 = lean_st_ref_get(x_8, x_11);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_ctor_get(x_154, 1);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unsigned_to_nat(8u);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_unsigned_to_nat(2u);
x_162 = lean_nat_shiftl(x_159, x_161);
x_163 = lean_unsigned_to_nat(3u);
x_164 = lean_nat_div(x_162, x_163);
lean_dec(x_162);
x_165 = l_Nat_nextPowerOfTwo(x_164);
lean_dec(x_164);
x_166 = lean_box(0);
x_167 = lean_mk_array(x_165, x_166);
lean_ctor_set(x_154, 1, x_167);
lean_ctor_set(x_154, 0, x_160);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_154);
lean_ctor_set(x_168, 1, x_158);
x_169 = l_Lean_Expr_hasFVar(x_152);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_Expr_hasMVar(x_152);
if (x_170 == 0)
{
lean_dec(x_152);
x_85 = x_107;
x_86 = x_113;
x_87 = x_153;
x_88 = x_157;
x_89 = x_110;
x_90 = x_170;
x_91 = x_168;
goto block_96;
}
else
{
lean_object* x_171; 
lean_inc(x_110);
lean_inc(x_113);
x_171 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_168);
x_97 = x_107;
x_98 = x_113;
x_99 = x_153;
x_100 = x_157;
x_101 = x_110;
x_102 = x_171;
goto block_106;
}
}
else
{
lean_object* x_172; 
lean_inc(x_110);
lean_inc(x_113);
x_172 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_168);
x_97 = x_107;
x_98 = x_113;
x_99 = x_153;
x_100 = x_157;
x_101 = x_110;
x_102 = x_172;
goto block_106;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_173 = lean_ctor_get(x_154, 0);
x_174 = lean_ctor_get(x_154, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_154);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_unsigned_to_nat(8u);
x_177 = lean_unsigned_to_nat(0u);
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_shiftl(x_176, x_178);
x_180 = lean_unsigned_to_nat(3u);
x_181 = lean_nat_div(x_179, x_180);
lean_dec(x_179);
x_182 = l_Nat_nextPowerOfTwo(x_181);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = lean_mk_array(x_182, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_175);
x_187 = l_Lean_Expr_hasFVar(x_152);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_152);
if (x_188 == 0)
{
lean_dec(x_152);
x_85 = x_107;
x_86 = x_113;
x_87 = x_153;
x_88 = x_174;
x_89 = x_110;
x_90 = x_188;
x_91 = x_186;
goto block_96;
}
else
{
lean_object* x_189; 
lean_inc(x_110);
lean_inc(x_113);
x_189 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_186);
x_97 = x_107;
x_98 = x_113;
x_99 = x_153;
x_100 = x_174;
x_101 = x_110;
x_102 = x_189;
goto block_106;
}
}
else
{
lean_object* x_190; 
lean_inc(x_110);
lean_inc(x_113);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_186);
x_97 = x_107;
x_98 = x_113;
x_99 = x_153;
x_100 = x_174;
x_101 = x_110;
x_102 = x_190;
goto block_106;
}
}
}
}
block_195:
{
if (x_193 == 0)
{
if (x_2 == 0)
{
x_107 = x_192;
x_108 = x_2;
goto block_191;
}
else
{
uint8_t x_194; 
x_194 = l_Lean_LocalDecl_isLet(x_26);
if (x_194 == 0)
{
x_107 = x_192;
x_108 = x_194;
goto block_191;
}
else
{
lean_dec(x_192);
lean_dec(x_26);
goto block_30;
}
}
}
else
{
lean_dec(x_192);
lean_dec(x_26);
goto block_30;
}
}
block_206:
{
lean_object* x_197; 
x_197 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_196);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
x_198 = l_Lean_LocalDecl_isAuxDecl(x_26);
if (x_198 == 0)
{
uint8_t x_199; uint8_t x_200; 
x_199 = l_Lean_LocalDecl_binderInfo(x_26);
x_200 = l_Lean_BinderInfo_isInstImplicit(x_199);
x_192 = x_196;
x_193 = x_200;
goto block_195;
}
else
{
x_192 = x_196;
x_193 = x_198;
goto block_195;
}
}
else
{
lean_object* x_201; uint8_t x_202; 
lean_dec(x_196);
lean_dec(x_26);
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
lean_dec(x_197);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_201, 0);
lean_dec(x_204);
lean_ctor_set(x_201, 1, x_28);
lean_ctor_set(x_201, 0, x_27);
x_15 = x_201;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_205; 
lean_dec(x_201);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_27);
lean_ctor_set(x_205, 1, x_28);
x_15 = x_205;
x_16 = x_11;
goto block_22;
}
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_5, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_20, x_17, x_8, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_array_size(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_12, x_15, x_17, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_23);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_free_object(x_4);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_array_size(x_33);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_usize_of_nat(x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_33, x_36, x_38, x_35, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_33);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_40);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; size_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
x_55 = lean_array_size(x_52);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_usize_of_nat(x_56);
x_58 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_2, x_52, x_55, x_57, x_54, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_52);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
lean_ctor_set(x_4, 0, x_63);
lean_ctor_set(x_58, 0, x_4);
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_ctor_set(x_4, 0, x_65);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_59);
lean_free_object(x_4);
x_67 = !lean_is_exclusive(x_58);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_58, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_69);
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_dec(x_58);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_4, 0);
lean_inc(x_73);
lean_dec(x_4);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
x_76 = lean_array_size(x_73);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_usize_of_nat(x_77);
x_79 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_2, x_73, x_76, x_78, x_75, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_73);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_88 = x_79;
} else {
 lean_dec_ref(x_79);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
lean_dec(x_81);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; 
x_11 = lean_box(0);
x_20 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_12 = x_21;
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_104; uint8_t x_105; lean_object* x_189; uint8_t x_190; lean_object* x_193; lean_object* x_204; 
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_204 = lean_ctor_get(x_23, 1);
lean_inc(x_204);
x_193 = x_204;
goto block_203;
block_27:
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_12 = x_26;
x_13 = x_8;
goto block_19;
}
block_35:
{
if (x_29 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
x_12 = x_31;
x_13 = x_30;
goto block_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_28);
x_32 = l_Lean_FVarIdSet_insert(x_24, x_28);
x_33 = l_Lean_FVarIdSet_insert(x_25, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_12 = x_34;
x_13 = x_30;
goto block_19;
}
}
block_50:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_st_ref_take(x_7, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
x_48 = lean_st_ref_set(x_7, x_47, x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_28 = x_36;
x_29 = x_38;
x_30 = x_49;
goto block_35;
}
block_58:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unbox(x_55);
lean_dec(x_55);
x_36 = x_51;
x_37 = x_52;
x_38 = x_57;
x_39 = x_56;
goto block_50;
}
block_74:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_take(x_7, x_60);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 4);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_69);
lean_ctor_set(x_71, 4, x_70);
x_72 = lean_st_ref_set(x_7, x_71, x_66);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_28 = x_59;
x_29 = x_61;
x_30 = x_73;
goto block_35;
}
block_81:
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_59 = x_75;
x_60 = x_76;
x_61 = x_80;
x_62 = x_79;
goto block_74;
}
block_93:
{
if (x_87 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasFVar(x_85);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Expr_hasMVar(x_85);
if (x_90 == 0)
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_82);
x_59 = x_83;
x_60 = x_84;
x_61 = x_90;
x_62 = x_88;
goto block_74;
}
else
{
lean_object* x_91; 
x_91 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_82, x_86, x_85, x_88);
x_75 = x_83;
x_76 = x_84;
x_77 = x_91;
goto block_81;
}
}
else
{
lean_object* x_92; 
x_92 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_82, x_86, x_85, x_88);
x_75 = x_83;
x_76 = x_84;
x_77 = x_92;
goto block_81;
}
}
else
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_82);
x_59 = x_83;
x_60 = x_84;
x_61 = x_87;
x_62 = x_88;
goto block_74;
}
}
block_103:
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_unbox(x_100);
lean_dec(x_100);
x_82 = x_95;
x_83 = x_94;
x_84 = x_96;
x_85 = x_97;
x_86 = x_98;
x_87 = x_102;
x_88 = x_101;
goto block_93;
}
block_188:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_box(x_105);
x_107 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_107, 0, x_106);
x_108 = lean_box(x_105);
x_109 = lean_box(x_9);
lean_inc(x_25);
x_110 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_110, 0, x_25);
lean_closure_set(x_110, 1, x_108);
lean_closure_set(x_110, 2, x_109);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_23, 3);
lean_inc(x_111);
lean_dec(x_23);
x_112 = lean_st_ref_get(x_7, x_8);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_unsigned_to_nat(8u);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_unsigned_to_nat(2u);
x_120 = lean_nat_shiftl(x_117, x_119);
x_121 = lean_unsigned_to_nat(3u);
x_122 = lean_nat_div(x_120, x_121);
lean_dec(x_120);
x_123 = l_Nat_nextPowerOfTwo(x_122);
lean_dec(x_122);
x_124 = lean_box(0);
x_125 = lean_mk_array(x_123, x_124);
lean_ctor_set(x_112, 1, x_125);
lean_ctor_set(x_112, 0, x_118);
lean_inc(x_116);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_116);
x_127 = l_Lean_Expr_hasFVar(x_111);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Expr_hasMVar(x_111);
if (x_128 == 0)
{
lean_dec(x_126);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_107);
x_36 = x_104;
x_37 = x_115;
x_38 = x_128;
x_39 = x_116;
goto block_50;
}
else
{
lean_object* x_129; 
lean_dec(x_116);
x_129 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_126);
x_51 = x_104;
x_52 = x_115;
x_53 = x_129;
goto block_58;
}
}
else
{
lean_object* x_130; 
lean_dec(x_116);
x_130 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_126);
x_51 = x_104;
x_52 = x_115;
x_53 = x_130;
goto block_58;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_131 = lean_ctor_get(x_112, 0);
x_132 = lean_ctor_get(x_112, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_112);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_unsigned_to_nat(8u);
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_unsigned_to_nat(2u);
x_137 = lean_nat_shiftl(x_134, x_136);
x_138 = lean_unsigned_to_nat(3u);
x_139 = lean_nat_div(x_137, x_138);
lean_dec(x_137);
x_140 = l_Nat_nextPowerOfTwo(x_139);
lean_dec(x_139);
x_141 = lean_box(0);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_142);
lean_inc(x_133);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_133);
x_145 = l_Lean_Expr_hasFVar(x_111);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = l_Lean_Expr_hasMVar(x_111);
if (x_146 == 0)
{
lean_dec(x_144);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_107);
x_36 = x_104;
x_37 = x_132;
x_38 = x_146;
x_39 = x_133;
goto block_50;
}
else
{
lean_object* x_147; 
lean_dec(x_133);
x_147 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_144);
x_51 = x_104;
x_52 = x_132;
x_53 = x_147;
goto block_58;
}
}
else
{
lean_object* x_148; 
lean_dec(x_133);
x_148 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_111, x_144);
x_51 = x_104;
x_52 = x_132;
x_53 = x_148;
goto block_58;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_23, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_23, 4);
lean_inc(x_150);
lean_dec(x_23);
x_151 = lean_st_ref_get(x_7, x_8);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_151, 1);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_unsigned_to_nat(8u);
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_nat_shiftl(x_156, x_158);
x_160 = lean_unsigned_to_nat(3u);
x_161 = lean_nat_div(x_159, x_160);
lean_dec(x_159);
x_162 = l_Nat_nextPowerOfTwo(x_161);
lean_dec(x_161);
x_163 = lean_box(0);
x_164 = lean_mk_array(x_162, x_163);
lean_ctor_set(x_151, 1, x_164);
lean_ctor_set(x_151, 0, x_157);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_151);
lean_ctor_set(x_165, 1, x_155);
x_166 = l_Lean_Expr_hasFVar(x_149);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = l_Lean_Expr_hasMVar(x_149);
if (x_167 == 0)
{
lean_dec(x_149);
x_82 = x_110;
x_83 = x_104;
x_84 = x_154;
x_85 = x_150;
x_86 = x_107;
x_87 = x_167;
x_88 = x_165;
goto block_93;
}
else
{
lean_object* x_168; 
lean_inc(x_107);
lean_inc(x_110);
x_168 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_165);
x_94 = x_104;
x_95 = x_110;
x_96 = x_154;
x_97 = x_150;
x_98 = x_107;
x_99 = x_168;
goto block_103;
}
}
else
{
lean_object* x_169; 
lean_inc(x_107);
lean_inc(x_110);
x_169 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_165);
x_94 = x_104;
x_95 = x_110;
x_96 = x_154;
x_97 = x_150;
x_98 = x_107;
x_99 = x_169;
goto block_103;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_170 = lean_ctor_get(x_151, 0);
x_171 = lean_ctor_get(x_151, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_151);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_unsigned_to_nat(8u);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_unsigned_to_nat(2u);
x_176 = lean_nat_shiftl(x_173, x_175);
x_177 = lean_unsigned_to_nat(3u);
x_178 = lean_nat_div(x_176, x_177);
lean_dec(x_176);
x_179 = l_Nat_nextPowerOfTwo(x_178);
lean_dec(x_178);
x_180 = lean_box(0);
x_181 = lean_mk_array(x_179, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_174);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_172);
x_184 = l_Lean_Expr_hasFVar(x_149);
if (x_184 == 0)
{
uint8_t x_185; 
x_185 = l_Lean_Expr_hasMVar(x_149);
if (x_185 == 0)
{
lean_dec(x_149);
x_82 = x_110;
x_83 = x_104;
x_84 = x_171;
x_85 = x_150;
x_86 = x_107;
x_87 = x_185;
x_88 = x_183;
goto block_93;
}
else
{
lean_object* x_186; 
lean_inc(x_107);
lean_inc(x_110);
x_186 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_183);
x_94 = x_104;
x_95 = x_110;
x_96 = x_171;
x_97 = x_150;
x_98 = x_107;
x_99 = x_186;
goto block_103;
}
}
else
{
lean_object* x_187; 
lean_inc(x_107);
lean_inc(x_110);
x_187 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_110, x_107, x_149, x_183);
x_94 = x_104;
x_95 = x_110;
x_96 = x_171;
x_97 = x_150;
x_98 = x_107;
x_99 = x_187;
goto block_103;
}
}
}
}
block_192:
{
if (x_190 == 0)
{
if (x_2 == 0)
{
x_104 = x_189;
x_105 = x_2;
goto block_188;
}
else
{
uint8_t x_191; 
x_191 = l_Lean_LocalDecl_isLet(x_23);
if (x_191 == 0)
{
x_104 = x_189;
x_105 = x_191;
goto block_188;
}
else
{
lean_dec(x_189);
lean_dec(x_23);
goto block_27;
}
}
}
else
{
lean_dec(x_189);
lean_dec(x_23);
goto block_27;
}
}
block_203:
{
lean_object* x_194; 
x_194 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_193);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = l_Lean_LocalDecl_isAuxDecl(x_23);
if (x_195 == 0)
{
uint8_t x_196; uint8_t x_197; 
x_196 = l_Lean_LocalDecl_binderInfo(x_23);
x_197 = l_Lean_BinderInfo_isInstImplicit(x_196);
x_189 = x_193;
x_190 = x_197;
goto block_192;
}
else
{
x_189 = x_193;
x_190 = x_195;
goto block_192;
}
}
else
{
lean_object* x_198; uint8_t x_199; 
lean_dec(x_193);
lean_dec(x_23);
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
lean_dec(x_194);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_198, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_198, 0);
lean_dec(x_201);
lean_ctor_set(x_198, 1, x_25);
lean_ctor_set(x_198, 0, x_24);
x_12 = x_198;
x_13 = x_8;
goto block_19;
}
else
{
lean_object* x_202; 
lean_dec(x_198);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_24);
lean_ctor_set(x_202, 1, x_25);
x_12 = x_202;
x_13 = x_8;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_14;
x_8 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_107; uint8_t x_108; lean_object* x_192; uint8_t x_193; lean_object* x_196; lean_object* x_207; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_207 = lean_ctor_get(x_26, 1);
lean_inc(x_207);
x_196 = x_207;
goto block_206;
block_30:
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_15 = x_29;
x_16 = x_11;
goto block_22;
}
block_38:
{
if (x_32 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
x_15 = x_34;
x_16 = x_33;
goto block_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_31);
x_35 = l_Lean_FVarIdSet_insert(x_27, x_31);
x_36 = l_Lean_FVarIdSet_insert(x_28, x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_15 = x_37;
x_16 = x_33;
goto block_22;
}
}
block_53:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_st_ref_take(x_8, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 4);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_st_ref_set(x_8, x_50, x_45);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_31 = x_39;
x_32 = x_41;
x_33 = x_52;
goto block_38;
}
block_61:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_39 = x_54;
x_40 = x_55;
x_41 = x_60;
x_42 = x_59;
goto block_53;
}
block_77:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_take(x_8, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 4);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
x_75 = lean_st_ref_set(x_8, x_74, x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_31 = x_62;
x_32 = x_64;
x_33 = x_76;
goto block_38;
}
block_84:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_62 = x_78;
x_63 = x_79;
x_64 = x_83;
x_65 = x_82;
goto block_77;
}
block_96:
{
if (x_90 == 0)
{
uint8_t x_92; 
x_92 = l_Lean_Expr_hasFVar(x_86);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = l_Lean_Expr_hasMVar(x_86);
if (x_93 == 0)
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
x_62 = x_85;
x_63 = x_89;
x_64 = x_93;
x_65 = x_91;
goto block_77;
}
else
{
lean_object* x_94; 
x_94 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_88, x_87, x_86, x_91);
x_78 = x_85;
x_79 = x_89;
x_80 = x_94;
goto block_84;
}
}
else
{
lean_object* x_95; 
x_95 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_88, x_87, x_86, x_91);
x_78 = x_85;
x_79 = x_89;
x_80 = x_95;
goto block_84;
}
}
else
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
x_62 = x_85;
x_63 = x_89;
x_64 = x_90;
x_65 = x_91;
goto block_77;
}
}
block_106:
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox(x_103);
lean_dec(x_103);
x_85 = x_98;
x_86 = x_97;
x_87 = x_99;
x_88 = x_101;
x_89 = x_100;
x_90 = x_105;
x_91 = x_104;
goto block_96;
}
block_191:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_box(x_108);
x_110 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = lean_box(x_108);
x_112 = lean_box(x_12);
lean_inc(x_28);
x_113 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_113, 0, x_28);
lean_closure_set(x_113, 1, x_111);
lean_closure_set(x_113, 2, x_112);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_26, 3);
lean_inc(x_114);
lean_dec(x_26);
x_115 = lean_st_ref_get(x_8, x_11);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_unsigned_to_nat(8u);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_shiftl(x_120, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = l_Nat_nextPowerOfTwo(x_125);
lean_dec(x_125);
x_127 = lean_box(0);
x_128 = lean_mk_array(x_126, x_127);
lean_ctor_set(x_115, 1, x_128);
lean_ctor_set(x_115, 0, x_121);
lean_inc(x_119);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_115);
lean_ctor_set(x_129, 1, x_119);
x_130 = l_Lean_Expr_hasFVar(x_114);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = l_Lean_Expr_hasMVar(x_114);
if (x_131 == 0)
{
lean_dec(x_129);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_110);
x_39 = x_107;
x_40 = x_118;
x_41 = x_131;
x_42 = x_119;
goto block_53;
}
else
{
lean_object* x_132; 
lean_dec(x_119);
x_132 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_129);
x_54 = x_107;
x_55 = x_118;
x_56 = x_132;
goto block_61;
}
}
else
{
lean_object* x_133; 
lean_dec(x_119);
x_133 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_129);
x_54 = x_107;
x_55 = x_118;
x_56 = x_133;
goto block_61;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_134 = lean_ctor_get(x_115, 0);
x_135 = lean_ctor_get(x_115, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_115);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_unsigned_to_nat(8u);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_shiftl(x_137, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = l_Nat_nextPowerOfTwo(x_142);
lean_dec(x_142);
x_144 = lean_box(0);
x_145 = lean_mk_array(x_143, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_138);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_136);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_136);
x_148 = l_Lean_Expr_hasFVar(x_114);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = l_Lean_Expr_hasMVar(x_114);
if (x_149 == 0)
{
lean_dec(x_147);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_110);
x_39 = x_107;
x_40 = x_135;
x_41 = x_149;
x_42 = x_136;
goto block_53;
}
else
{
lean_object* x_150; 
lean_dec(x_136);
x_150 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_147);
x_54 = x_107;
x_55 = x_135;
x_56 = x_150;
goto block_61;
}
}
else
{
lean_object* x_151; 
lean_dec(x_136);
x_151 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_114, x_147);
x_54 = x_107;
x_55 = x_135;
x_56 = x_151;
goto block_61;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_26, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_26, 4);
lean_inc(x_153);
lean_dec(x_26);
x_154 = lean_st_ref_get(x_8, x_11);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_ctor_get(x_154, 1);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unsigned_to_nat(8u);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_unsigned_to_nat(2u);
x_162 = lean_nat_shiftl(x_159, x_161);
x_163 = lean_unsigned_to_nat(3u);
x_164 = lean_nat_div(x_162, x_163);
lean_dec(x_162);
x_165 = l_Nat_nextPowerOfTwo(x_164);
lean_dec(x_164);
x_166 = lean_box(0);
x_167 = lean_mk_array(x_165, x_166);
lean_ctor_set(x_154, 1, x_167);
lean_ctor_set(x_154, 0, x_160);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_154);
lean_ctor_set(x_168, 1, x_158);
x_169 = l_Lean_Expr_hasFVar(x_152);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_Expr_hasMVar(x_152);
if (x_170 == 0)
{
lean_dec(x_152);
x_85 = x_107;
x_86 = x_153;
x_87 = x_110;
x_88 = x_113;
x_89 = x_157;
x_90 = x_170;
x_91 = x_168;
goto block_96;
}
else
{
lean_object* x_171; 
lean_inc(x_110);
lean_inc(x_113);
x_171 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_168);
x_97 = x_153;
x_98 = x_107;
x_99 = x_110;
x_100 = x_157;
x_101 = x_113;
x_102 = x_171;
goto block_106;
}
}
else
{
lean_object* x_172; 
lean_inc(x_110);
lean_inc(x_113);
x_172 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_168);
x_97 = x_153;
x_98 = x_107;
x_99 = x_110;
x_100 = x_157;
x_101 = x_113;
x_102 = x_172;
goto block_106;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_173 = lean_ctor_get(x_154, 0);
x_174 = lean_ctor_get(x_154, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_154);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_unsigned_to_nat(8u);
x_177 = lean_unsigned_to_nat(0u);
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_shiftl(x_176, x_178);
x_180 = lean_unsigned_to_nat(3u);
x_181 = lean_nat_div(x_179, x_180);
lean_dec(x_179);
x_182 = l_Nat_nextPowerOfTwo(x_181);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = lean_mk_array(x_182, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_175);
x_187 = l_Lean_Expr_hasFVar(x_152);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = l_Lean_Expr_hasMVar(x_152);
if (x_188 == 0)
{
lean_dec(x_152);
x_85 = x_107;
x_86 = x_153;
x_87 = x_110;
x_88 = x_113;
x_89 = x_174;
x_90 = x_188;
x_91 = x_186;
goto block_96;
}
else
{
lean_object* x_189; 
lean_inc(x_110);
lean_inc(x_113);
x_189 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_186);
x_97 = x_153;
x_98 = x_107;
x_99 = x_110;
x_100 = x_174;
x_101 = x_113;
x_102 = x_189;
goto block_106;
}
}
else
{
lean_object* x_190; 
lean_inc(x_110);
lean_inc(x_113);
x_190 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_113, x_110, x_152, x_186);
x_97 = x_153;
x_98 = x_107;
x_99 = x_110;
x_100 = x_174;
x_101 = x_113;
x_102 = x_190;
goto block_106;
}
}
}
}
block_195:
{
if (x_193 == 0)
{
if (x_2 == 0)
{
x_107 = x_192;
x_108 = x_2;
goto block_191;
}
else
{
uint8_t x_194; 
x_194 = l_Lean_LocalDecl_isLet(x_26);
if (x_194 == 0)
{
x_107 = x_192;
x_108 = x_194;
goto block_191;
}
else
{
lean_dec(x_192);
lean_dec(x_26);
goto block_30;
}
}
}
else
{
lean_dec(x_192);
lean_dec(x_26);
goto block_30;
}
}
block_206:
{
lean_object* x_197; 
x_197 = l_Lean_RBNode_findCore___at___Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(x_1, x_196);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
x_198 = l_Lean_LocalDecl_isAuxDecl(x_26);
if (x_198 == 0)
{
uint8_t x_199; uint8_t x_200; 
x_199 = l_Lean_LocalDecl_binderInfo(x_26);
x_200 = l_Lean_BinderInfo_isInstImplicit(x_199);
x_192 = x_196;
x_193 = x_200;
goto block_195;
}
else
{
x_192 = x_196;
x_193 = x_198;
goto block_195;
}
}
else
{
lean_object* x_201; uint8_t x_202; 
lean_dec(x_196);
lean_dec(x_26);
x_201 = lean_ctor_get(x_197, 0);
lean_inc(x_201);
lean_dec(x_197);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_201, 0);
lean_dec(x_204);
lean_ctor_set(x_201, 1, x_28);
lean_ctor_set(x_201, 0, x_27);
x_15 = x_201;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_205; 
lean_dec(x_201);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_27);
lean_ctor_set(x_205, 1, x_28);
x_15 = x_205;
x_16 = x_11;
goto block_22;
}
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_5, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_20, x_17, x_8, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_inc(x_4);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_size(x_21);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_usize_of_nat(x_25);
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(x_1, x_2, x_21, x_24, x_26, x_23, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Expr_isFVar(x_12);
if (x_13 == 0)
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_fvarId_x21(x_12);
lean_dec(x_12);
x_15 = l_Lean_FVarIdSet_insert(x_4, x_14);
x_5 = x_15;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = lean_box(0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_1);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
x_10 = x_9;
goto block_22;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
x_10 = x_9;
goto block_22;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_23);
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(x_1, x_27, x_28, x_9);
x_10 = x_29;
goto block_22;
}
}
block_22:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(x_2, x_3, x_13, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__0(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___lam__1(x_1, x_5, x_6, x_4);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_9, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1_spec__1(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___redArg(x_1, x_9, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4_spec__4(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0_spec__4(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_PersistentArray_forIn___at___Lean_Meta_getFVarSetToGeneralize_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_getFVarSetToGeneralize_spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarSetToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_1, x_3);
x_7 = lean_array_push(x_6, x_4);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toArray___at___Lean_Meta_getFVarsToGeneralize_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Lean_RBNode_fold___at___Lean_RBTree_toArray___at___Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_mkGeneralizationForbiddenSet(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
x_12 = l_Lean_Meta_getFVarSetToGeneralize(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_RBTree_toArray___at___Lean_Meta_getFVarsToGeneralize_spec__0(x_13);
x_16 = l_Lean_Meta_sortFVarIds___redArg(x_15, x_4, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFVarsToGeneralize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_getFVarsToGeneralize(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
