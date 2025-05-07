// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MarkNestedProofs
// Imports: Init.Grind.Util Lean.Util.PtrSet Lean.Meta.Transform Lean.Meta.Basic Lean.Meta.InferType Lean.Meta.Tactic.Grind.Util
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_mkPtrMap(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ptr_addr(x_5);
x_9 = lean_ptr_addr(x_1);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_11);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_ptr_addr(x_12);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_14);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_lt(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_array_get(x_14, x_15, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_17 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_25; size_t x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_25 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_26 = lean_ptr_addr(x_18);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_28 = lean_array_set(x_15, x_4, x_18);
x_29 = lean_box(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_20 = x_30;
goto block_24;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_18);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
x_20 = x_32;
goto block_24;
}
block_24:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_22;
x_10 = x_19;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_array_set(x_5, x_6, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_6, x_16);
lean_dec(x_6);
x_4 = x_13;
x_5 = x_15;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_box(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(x_2, x_22, x_24, x_19, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_26);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_mkAppN(x_4, x_35);
lean_dec(x_35);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_dec(x_26);
x_39 = l_Lean_mkAppN(x_4, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_12 = l_instMonadEIO(lean_box(0));
x_13 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
x_30 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_24);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_27);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
x_44 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_43);
x_45 = l_Lean_instInhabitedExpr;
x_46 = l_instInhabitedOfMonad___redArg(x_44, x_45);
x_47 = lean_panic_fn(x_46, x_1);
x_48 = lean_apply_6(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
return x_48;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_19; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; uint64_t x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; lean_object* x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; uint8_t x_43; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_ptr_addr(x_1);
x_24 = lean_usize_to_uint64(x_23);
x_25 = lean_unsigned_to_nat(11u);
x_26 = lean_uint64_of_nat(x_25);
x_27 = lean_uint64_mix_hash(x_24, x_26);
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_unsigned_to_nat(16u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_sub(x_37, x_39);
x_41 = lean_usize_land(x_36, x_40);
x_42 = lean_array_uget(x_21, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_nat_add(x_20, x_38);
lean_dec(x_20);
lean_inc(x_2);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set(x_45, 2, x_42);
x_46 = lean_array_uset(x_21, x_41, x_45);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_shiftl(x_44, x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_div(x_48, x_49);
lean_dec(x_48);
x_51 = lean_array_get_size(x_46);
x_52 = lean_nat_dec_le(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_46);
lean_ctor_set(x_10, 1, x_53);
lean_ctor_set(x_10, 0, x_44);
x_12 = x_10;
goto block_18;
}
else
{
lean_ctor_set(x_10, 1, x_46);
lean_ctor_set(x_10, 0, x_44);
x_12 = x_10;
goto block_18;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_box(0);
x_55 = lean_array_uset(x_21, x_41, x_54);
lean_inc(x_2);
x_56 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_42);
x_57 = lean_array_uset(x_55, x_41, x_56);
lean_ctor_set(x_10, 1, x_57);
x_12 = x_10;
goto block_18;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; uint64_t x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; size_t x_74; size_t x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_58 = lean_ctor_get(x_10, 0);
x_59 = lean_ctor_get(x_10, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_10);
x_60 = lean_array_get_size(x_59);
x_61 = lean_ptr_addr(x_1);
x_62 = lean_usize_to_uint64(x_61);
x_63 = lean_unsigned_to_nat(11u);
x_64 = lean_uint64_of_nat(x_63);
x_65 = lean_uint64_mix_hash(x_62, x_64);
x_66 = lean_unsigned_to_nat(32u);
x_67 = lean_uint64_of_nat(x_66);
x_68 = lean_uint64_shift_right(x_65, x_67);
x_69 = lean_uint64_xor(x_65, x_68);
x_70 = lean_unsigned_to_nat(16u);
x_71 = lean_uint64_of_nat(x_70);
x_72 = lean_uint64_shift_right(x_69, x_71);
x_73 = lean_uint64_xor(x_69, x_72);
x_74 = lean_uint64_to_usize(x_73);
x_75 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_usize_of_nat(x_76);
x_78 = lean_usize_sub(x_75, x_77);
x_79 = lean_usize_land(x_74, x_78);
x_80 = lean_array_uget(x_59, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_nat_add(x_58, x_76);
lean_dec(x_58);
lean_inc(x_2);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_2);
lean_ctor_set(x_83, 2, x_80);
x_84 = lean_array_uset(x_59, x_79, x_83);
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_shiftl(x_82, x_85);
x_87 = lean_unsigned_to_nat(3u);
x_88 = lean_nat_div(x_86, x_87);
lean_dec(x_86);
x_89 = lean_array_get_size(x_84);
x_90 = lean_nat_dec_le(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_84);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_91);
x_12 = x_92;
goto block_18;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_84);
x_12 = x_93;
goto block_18;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_box(0);
x_95 = lean_array_uset(x_59, x_79, x_94);
lean_inc(x_2);
x_96 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_2, x_80);
x_97 = lean_array_uset(x_95, x_79, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_58);
lean_ctor_set(x_98, 1, x_97);
x_12 = x_98;
goto block_18;
}
}
block_18:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_set(x_3, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_isProof(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_64; uint8_t x_207; uint8_t x_211; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_211 = lean_unbox(x_9);
if (x_211 == 0)
{
uint8_t x_212; 
x_212 = l_Lean_Expr_isApp(x_1);
if (x_212 == 0)
{
uint8_t x_213; 
x_213 = l_Lean_Expr_isForall(x_1);
x_207 = x_213;
goto block_210;
}
else
{
x_207 = x_212;
goto block_210;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_dec(x_11);
lean_dec(x_9);
x_214 = lean_mk_string_unchecked("Lean", 4, 4);
x_215 = lean_mk_string_unchecked("Grind", 5, 5);
x_216 = lean_mk_string_unchecked("nestedProof", 11, 11);
x_217 = l_Lean_Name_mkStr3(x_214, x_215, x_216);
x_218 = l_Lean_Expr_isAppOf(x_1, x_217);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_st_ref_get(x_2, x_10);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; size_t x_225; uint64_t x_226; lean_object* x_227; uint64_t x_228; uint64_t x_229; lean_object* x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; lean_object* x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; size_t x_238; size_t x_239; lean_object* x_240; size_t x_241; size_t x_242; size_t x_243; lean_object* x_244; lean_object* x_245; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_ctor_get(x_219, 1);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_array_get_size(x_223);
x_225 = lean_ptr_addr(x_1);
x_226 = lean_usize_to_uint64(x_225);
x_227 = lean_unsigned_to_nat(11u);
x_228 = lean_uint64_of_nat(x_227);
x_229 = lean_uint64_mix_hash(x_226, x_228);
x_230 = lean_unsigned_to_nat(32u);
x_231 = lean_uint64_of_nat(x_230);
x_232 = lean_uint64_shift_right(x_229, x_231);
x_233 = lean_uint64_xor(x_229, x_232);
x_234 = lean_unsigned_to_nat(16u);
x_235 = lean_uint64_of_nat(x_234);
x_236 = lean_uint64_shift_right(x_233, x_235);
x_237 = lean_uint64_xor(x_233, x_236);
x_238 = lean_uint64_to_usize(x_237);
x_239 = lean_usize_of_nat(x_224);
lean_dec(x_224);
x_240 = lean_unsigned_to_nat(1u);
x_241 = lean_usize_of_nat(x_240);
x_242 = lean_usize_sub(x_239, x_241);
x_243 = lean_usize_land(x_238, x_242);
x_244 = lean_array_uget(x_223, x_243);
lean_dec(x_223);
x_245 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_244);
lean_dec(x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
lean_free_object(x_219);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_246 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_222);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_249 = l_Lean_Meta_Grind_unfoldReducible(x_247, x_3, x_4, x_5, x_6, x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc(x_6);
lean_inc(x_5);
x_252 = l_Lean_Core_betaReduce(x_250, x_5, x_6, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
lean_inc(x_2);
x_255 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_253, x_2, x_3, x_4, x_5, x_6, x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_st_ref_take(x_2, x_257);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = !lean_is_exclusive(x_259);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_274; size_t x_275; size_t x_276; size_t x_277; lean_object* x_278; uint8_t x_279; 
x_262 = lean_ctor_get(x_259, 0);
x_263 = lean_ctor_get(x_259, 1);
x_264 = lean_box(0);
x_265 = l_Lean_Expr_const___override(x_217, x_264);
lean_inc(x_1);
x_266 = l_Lean_mkAppB(x_265, x_256, x_1);
x_274 = lean_array_get_size(x_263);
x_275 = lean_usize_of_nat(x_274);
lean_dec(x_274);
x_276 = lean_usize_sub(x_275, x_241);
x_277 = lean_usize_land(x_238, x_276);
x_278 = lean_array_uget(x_263, x_277);
x_279 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_280 = lean_nat_add(x_262, x_240);
lean_dec(x_262);
lean_inc(x_266);
x_281 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_281, 0, x_1);
lean_ctor_set(x_281, 1, x_266);
lean_ctor_set(x_281, 2, x_278);
x_282 = lean_array_uset(x_263, x_277, x_281);
x_283 = lean_unsigned_to_nat(2u);
x_284 = lean_nat_shiftl(x_280, x_283);
x_285 = lean_unsigned_to_nat(3u);
x_286 = lean_nat_div(x_284, x_285);
lean_dec(x_284);
x_287 = lean_array_get_size(x_282);
x_288 = lean_nat_dec_le(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
if (x_288 == 0)
{
lean_object* x_289; 
x_289 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_282);
lean_ctor_set(x_259, 1, x_289);
lean_ctor_set(x_259, 0, x_280);
x_267 = x_259;
goto block_273;
}
else
{
lean_ctor_set(x_259, 1, x_282);
lean_ctor_set(x_259, 0, x_280);
x_267 = x_259;
goto block_273;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_box(0);
x_291 = lean_array_uset(x_263, x_277, x_290);
lean_inc(x_266);
x_292 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_266, x_278);
x_293 = lean_array_uset(x_291, x_277, x_292);
lean_ctor_set(x_259, 1, x_293);
x_267 = x_259;
goto block_273;
}
block_273:
{
lean_object* x_268; uint8_t x_269; 
x_268 = lean_st_ref_set(x_2, x_267, x_260);
lean_dec(x_2);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
lean_ctor_set(x_268, 0, x_266);
return x_268;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_266);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_305; size_t x_306; size_t x_307; size_t x_308; lean_object* x_309; uint8_t x_310; 
x_294 = lean_ctor_get(x_259, 0);
x_295 = lean_ctor_get(x_259, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_259);
x_296 = lean_box(0);
x_297 = l_Lean_Expr_const___override(x_217, x_296);
lean_inc(x_1);
x_298 = l_Lean_mkAppB(x_297, x_256, x_1);
x_305 = lean_array_get_size(x_295);
x_306 = lean_usize_of_nat(x_305);
lean_dec(x_305);
x_307 = lean_usize_sub(x_306, x_241);
x_308 = lean_usize_land(x_238, x_307);
x_309 = lean_array_uget(x_295, x_308);
x_310 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_311 = lean_nat_add(x_294, x_240);
lean_dec(x_294);
lean_inc(x_298);
x_312 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_312, 0, x_1);
lean_ctor_set(x_312, 1, x_298);
lean_ctor_set(x_312, 2, x_309);
x_313 = lean_array_uset(x_295, x_308, x_312);
x_314 = lean_unsigned_to_nat(2u);
x_315 = lean_nat_shiftl(x_311, x_314);
x_316 = lean_unsigned_to_nat(3u);
x_317 = lean_nat_div(x_315, x_316);
lean_dec(x_315);
x_318 = lean_array_get_size(x_313);
x_319 = lean_nat_dec_le(x_317, x_318);
lean_dec(x_318);
lean_dec(x_317);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_313);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_311);
lean_ctor_set(x_321, 1, x_320);
x_299 = x_321;
goto block_304;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_311);
lean_ctor_set(x_322, 1, x_313);
x_299 = x_322;
goto block_304;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_323 = lean_box(0);
x_324 = lean_array_uset(x_295, x_308, x_323);
lean_inc(x_298);
x_325 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_298, x_309);
x_326 = lean_array_uset(x_324, x_308, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_294);
lean_ctor_set(x_327, 1, x_326);
x_299 = x_327;
goto block_304;
}
block_304:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_st_ref_set(x_2, x_299, x_260);
lean_dec(x_2);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_302 = x_300;
} else {
 lean_dec_ref(x_300);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_298);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
else
{
lean_dec(x_217);
lean_dec(x_2);
lean_dec(x_1);
return x_255;
}
}
else
{
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_252;
}
}
else
{
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_249;
}
}
else
{
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_246;
}
}
else
{
lean_object* x_328; 
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_328 = lean_ctor_get(x_245, 0);
lean_inc(x_328);
lean_dec(x_245);
lean_ctor_set(x_219, 0, x_328);
return x_219;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; size_t x_333; uint64_t x_334; lean_object* x_335; uint64_t x_336; uint64_t x_337; lean_object* x_338; uint64_t x_339; uint64_t x_340; uint64_t x_341; lean_object* x_342; uint64_t x_343; uint64_t x_344; uint64_t x_345; size_t x_346; size_t x_347; lean_object* x_348; size_t x_349; size_t x_350; size_t x_351; lean_object* x_352; lean_object* x_353; 
x_329 = lean_ctor_get(x_219, 0);
x_330 = lean_ctor_get(x_219, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_219);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_array_get_size(x_331);
x_333 = lean_ptr_addr(x_1);
x_334 = lean_usize_to_uint64(x_333);
x_335 = lean_unsigned_to_nat(11u);
x_336 = lean_uint64_of_nat(x_335);
x_337 = lean_uint64_mix_hash(x_334, x_336);
x_338 = lean_unsigned_to_nat(32u);
x_339 = lean_uint64_of_nat(x_338);
x_340 = lean_uint64_shift_right(x_337, x_339);
x_341 = lean_uint64_xor(x_337, x_340);
x_342 = lean_unsigned_to_nat(16u);
x_343 = lean_uint64_of_nat(x_342);
x_344 = lean_uint64_shift_right(x_341, x_343);
x_345 = lean_uint64_xor(x_341, x_344);
x_346 = lean_uint64_to_usize(x_345);
x_347 = lean_usize_of_nat(x_332);
lean_dec(x_332);
x_348 = lean_unsigned_to_nat(1u);
x_349 = lean_usize_of_nat(x_348);
x_350 = lean_usize_sub(x_347, x_349);
x_351 = lean_usize_land(x_346, x_350);
x_352 = lean_array_uget(x_331, x_351);
lean_dec(x_331);
x_353 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_352);
lean_dec(x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_354 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_330);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_357 = l_Lean_Meta_Grind_unfoldReducible(x_355, x_3, x_4, x_5, x_6, x_356);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
lean_inc(x_6);
lean_inc(x_5);
x_360 = l_Lean_Core_betaReduce(x_358, x_5, x_6, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
lean_inc(x_2);
x_363 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_361, x_2, x_3, x_4, x_5, x_6, x_362);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_381; size_t x_382; size_t x_383; size_t x_384; lean_object* x_385; uint8_t x_386; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_st_ref_take(x_2, x_365);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_371 = x_367;
} else {
 lean_dec_ref(x_367);
 x_371 = lean_box(0);
}
x_372 = lean_box(0);
x_373 = l_Lean_Expr_const___override(x_217, x_372);
lean_inc(x_1);
x_374 = l_Lean_mkAppB(x_373, x_364, x_1);
x_381 = lean_array_get_size(x_370);
x_382 = lean_usize_of_nat(x_381);
lean_dec(x_381);
x_383 = lean_usize_sub(x_382, x_349);
x_384 = lean_usize_land(x_346, x_383);
x_385 = lean_array_uget(x_370, x_384);
x_386 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_NumObjs_visit_spec__0___redArg(x_1, x_385);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_387 = lean_nat_add(x_369, x_348);
lean_dec(x_369);
lean_inc(x_374);
x_388 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_388, 0, x_1);
lean_ctor_set(x_388, 1, x_374);
lean_ctor_set(x_388, 2, x_385);
x_389 = lean_array_uset(x_370, x_384, x_388);
x_390 = lean_unsigned_to_nat(2u);
x_391 = lean_nat_shiftl(x_387, x_390);
x_392 = lean_unsigned_to_nat(3u);
x_393 = lean_nat_div(x_391, x_392);
lean_dec(x_391);
x_394 = lean_array_get_size(x_389);
x_395 = lean_nat_dec_le(x_393, x_394);
lean_dec(x_394);
lean_dec(x_393);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
x_396 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_NumObjs_visit_spec__1___redArg(x_389);
if (lean_is_scalar(x_371)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_371;
}
lean_ctor_set(x_397, 0, x_387);
lean_ctor_set(x_397, 1, x_396);
x_375 = x_397;
goto block_380;
}
else
{
lean_object* x_398; 
if (lean_is_scalar(x_371)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_371;
}
lean_ctor_set(x_398, 0, x_387);
lean_ctor_set(x_398, 1, x_389);
x_375 = x_398;
goto block_380;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = lean_box(0);
x_400 = lean_array_uset(x_370, x_384, x_399);
lean_inc(x_374);
x_401 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__0___redArg(x_1, x_374, x_385);
x_402 = lean_array_uset(x_400, x_384, x_401);
if (lean_is_scalar(x_371)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_371;
}
lean_ctor_set(x_403, 0, x_369);
lean_ctor_set(x_403, 1, x_402);
x_375 = x_403;
goto block_380;
}
block_380:
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_376 = lean_st_ref_set(x_2, x_375, x_368);
lean_dec(x_2);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_374);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
else
{
lean_dec(x_217);
lean_dec(x_2);
lean_dec(x_1);
return x_363;
}
}
else
{
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_360;
}
}
else
{
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_357;
}
}
else
{
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_354;
}
}
else
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_404 = lean_ctor_get(x_353, 0);
lean_inc(x_404);
lean_dec(x_353);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_330);
return x_405;
}
}
}
else
{
lean_object* x_406; 
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_1);
lean_ctor_set(x_406, 1, x_10);
return x_406;
}
}
block_31:
{
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
x_25 = l_Lean_Expr_forallE___override(x_19, x_18, x_21, x_16);
x_26 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_25, x_13, x_23, x_12, x_15, x_17, x_22);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_23);
lean_dec(x_13);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_20, x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_28 = l_Lean_Expr_forallE___override(x_19, x_18, x_21, x_16);
x_29 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_28, x_13, x_23, x_12, x_15, x_17, x_22);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_23);
lean_dec(x_13);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
x_30 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_14, x_13, x_23, x_12, x_15, x_17, x_22);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_23);
lean_dec(x_13);
return x_30;
}
}
}
block_63:
{
lean_object* x_44; 
x_44 = l_Lean_Expr_forallE___override(x_33, x_32, x_35, x_34);
if (lean_obj_tag(x_44) == 7)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; size_t x_49; size_t x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_44, sizeof(void*)*3 + 8);
x_49 = lean_ptr_addr(x_46);
lean_dec(x_46);
x_50 = lean_ptr_addr(x_36);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_dec(x_47);
x_12 = x_40;
x_13 = x_38;
x_14 = x_44;
x_15 = x_41;
x_16 = x_34;
x_17 = x_42;
x_18 = x_36;
x_19 = x_45;
x_20 = x_48;
x_21 = x_37;
x_22 = x_43;
x_23 = x_39;
x_24 = x_51;
goto block_31;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_53 = lean_ptr_addr(x_37);
x_54 = lean_usize_dec_eq(x_52, x_53);
x_12 = x_40;
x_13 = x_38;
x_14 = x_44;
x_15 = x_41;
x_16 = x_34;
x_17 = x_42;
x_18 = x_36;
x_19 = x_45;
x_20 = x_48;
x_21 = x_37;
x_22 = x_43;
x_23 = x_39;
x_24 = x_54;
goto block_31;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_36);
x_55 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_56 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_57 = lean_unsigned_to_nat(1828u);
x_58 = lean_unsigned_to_nat(23u);
x_59 = lean_mk_string_unchecked("forall expected", 15, 15);
x_60 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_55, x_56, x_57, x_58, x_59);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_55);
x_61 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_60);
x_62 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_61, x_38, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
return x_62;
}
}
block_206:
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_st_ref_get(x_2, x_10);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; uint64_t x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; lean_object* x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; size_t x_84; size_t x_85; lean_object* x_86; size_t x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_array_get_size(x_69);
x_71 = lean_ptr_addr(x_1);
x_72 = lean_usize_to_uint64(x_71);
x_73 = lean_unsigned_to_nat(11u);
x_74 = lean_uint64_of_nat(x_73);
x_75 = lean_uint64_mix_hash(x_72, x_74);
x_76 = lean_unsigned_to_nat(32u);
x_77 = lean_uint64_of_nat(x_76);
x_78 = lean_uint64_shift_right(x_75, x_77);
x_79 = lean_uint64_xor(x_75, x_78);
x_80 = lean_unsigned_to_nat(16u);
x_81 = lean_uint64_of_nat(x_80);
x_82 = lean_uint64_shift_right(x_79, x_81);
x_83 = lean_uint64_xor(x_79, x_82);
x_84 = lean_uint64_to_usize(x_83);
x_85 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_usize_of_nat(x_86);
x_88 = lean_usize_sub(x_85, x_87);
x_89 = lean_usize_land(x_84, x_88);
x_90 = lean_array_uget(x_69, x_89);
lean_dec(x_69);
x_91 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_free_object(x_65);
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_92 = lean_box(0);
x_93 = l_Lean_Expr_sort___override(x_92);
x_94 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_94);
x_95 = lean_mk_array(x_94, x_93);
x_96 = lean_nat_sub(x_94, x_86);
lean_dec(x_94);
x_97 = lean_unbox(x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_1, 2);
x_98 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(x_97, x_64, x_1, x_1, x_95, x_96, x_2, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_99, x_2, x_3, x_4, x_5, x_6, x_100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_101;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_98;
}
}
case 7:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
lean_dec(x_9);
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 2);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_103);
x_106 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_103, x_2, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Expr_hasLooseBVars(x_104);
if (x_109 == 0)
{
lean_object* x_110; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_104);
x_110 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_104, x_2, x_3, x_4, x_5, x_6, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_32 = x_103;
x_33 = x_102;
x_34 = x_105;
x_35 = x_104;
x_36 = x_107;
x_37 = x_111;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_112;
goto block_63;
}
else
{
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_110;
}
}
else
{
lean_inc(x_104);
x_32 = x_103;
x_33 = x_102;
x_34 = x_105;
x_35 = x_104;
x_36 = x_107;
x_37 = x_104;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_108;
goto block_63;
}
}
else
{
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_106;
}
}
case 11:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_9);
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 2);
lean_inc(x_115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_115);
x_116 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_115, x_2, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; size_t x_119; size_t x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ptr_addr(x_115);
lean_dec(x_115);
x_120 = lean_ptr_addr(x_117);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Lean_Expr_proj___override(x_113, x_114, x_117);
x_123 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_122, x_2, x_3, x_4, x_5, x_6, x_118);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_123;
}
else
{
lean_object* x_124; 
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_113);
lean_inc(x_1);
x_124 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_118);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_124;
}
}
else
{
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_116;
}
}
default: 
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_9);
x_125 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.MarkNestedProofs", 39, 39);
x_126 = lean_mk_string_unchecked("Lean.Meta.Grind.markNestedProofsImpl.visit", 42, 42);
x_127 = lean_unsigned_to_nat(68u);
x_128 = lean_unsigned_to_nat(13u);
x_129 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_130 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_125, x_126, x_127, x_128, x_129);
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_125);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_131 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(x_130, x_2, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_132, x_2, x_3, x_4, x_5, x_6, x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_134;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_131;
}
}
}
}
else
{
lean_object* x_135; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_ctor_get(x_91, 0);
lean_inc(x_135);
lean_dec(x_91);
lean_ctor_set(x_65, 0, x_135);
return x_65;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; uint64_t x_141; lean_object* x_142; uint64_t x_143; uint64_t x_144; lean_object* x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; lean_object* x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; size_t x_153; size_t x_154; lean_object* x_155; size_t x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; 
x_136 = lean_ctor_get(x_65, 0);
x_137 = lean_ctor_get(x_65, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_65);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_array_get_size(x_138);
x_140 = lean_ptr_addr(x_1);
x_141 = lean_usize_to_uint64(x_140);
x_142 = lean_unsigned_to_nat(11u);
x_143 = lean_uint64_of_nat(x_142);
x_144 = lean_uint64_mix_hash(x_141, x_143);
x_145 = lean_unsigned_to_nat(32u);
x_146 = lean_uint64_of_nat(x_145);
x_147 = lean_uint64_shift_right(x_144, x_146);
x_148 = lean_uint64_xor(x_144, x_147);
x_149 = lean_unsigned_to_nat(16u);
x_150 = lean_uint64_of_nat(x_149);
x_151 = lean_uint64_shift_right(x_148, x_150);
x_152 = lean_uint64_xor(x_148, x_151);
x_153 = lean_uint64_to_usize(x_152);
x_154 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_usize_of_nat(x_155);
x_157 = lean_usize_sub(x_154, x_156);
x_158 = lean_usize_land(x_153, x_157);
x_159 = lean_array_uget(x_138, x_158);
lean_dec(x_138);
x_160 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_159);
lean_dec(x_159);
if (lean_obj_tag(x_160) == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_161 = lean_box(0);
x_162 = l_Lean_Expr_sort___override(x_161);
x_163 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_163);
x_164 = lean_mk_array(x_163, x_162);
x_165 = lean_nat_sub(x_163, x_155);
lean_dec(x_163);
x_166 = lean_unbox(x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_n(x_1, 2);
x_167 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(x_166, x_64, x_1, x_1, x_164, x_165, x_2, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_168, x_2, x_3, x_4, x_5, x_6, x_169);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_170;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_167;
}
}
case 7:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
lean_dec(x_9);
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_1, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 2);
lean_inc(x_173);
x_174 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_172);
x_175 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_172, x_2, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_Expr_hasLooseBVars(x_173);
if (x_178 == 0)
{
lean_object* x_179; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_173);
x_179 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_173, x_2, x_3, x_4, x_5, x_6, x_177);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_32 = x_172;
x_33 = x_171;
x_34 = x_174;
x_35 = x_173;
x_36 = x_176;
x_37 = x_180;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_181;
goto block_63;
}
else
{
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_179;
}
}
else
{
lean_inc(x_173);
x_32 = x_172;
x_33 = x_171;
x_34 = x_174;
x_35 = x_173;
x_36 = x_176;
x_37 = x_173;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_177;
goto block_63;
}
}
else
{
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_175;
}
}
case 11:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_9);
x_182 = lean_ctor_get(x_1, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_1, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_1, 2);
lean_inc(x_184);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_184);
x_185 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_184, x_2, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; size_t x_188; size_t x_189; uint8_t x_190; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ptr_addr(x_184);
lean_dec(x_184);
x_189 = lean_ptr_addr(x_186);
x_190 = lean_usize_dec_eq(x_188, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = l_Lean_Expr_proj___override(x_182, x_183, x_186);
x_192 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_191, x_2, x_3, x_4, x_5, x_6, x_187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_192;
}
else
{
lean_object* x_193; 
lean_dec(x_186);
lean_dec(x_183);
lean_dec(x_182);
lean_inc(x_1);
x_193 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_1, x_2, x_3, x_4, x_5, x_6, x_187);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_193;
}
}
else
{
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_185;
}
}
default: 
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_9);
x_194 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.MarkNestedProofs", 39, 39);
x_195 = lean_mk_string_unchecked("Lean.Meta.Grind.markNestedProofsImpl.visit", 42, 42);
x_196 = lean_unsigned_to_nat(68u);
x_197 = lean_unsigned_to_nat(13u);
x_198 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_199 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_194, x_195, x_196, x_197, x_198);
lean_dec(x_198);
lean_dec(x_195);
lean_dec(x_194);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_200 = l_panic___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__4(x_199, x_2, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_201, x_2, x_3, x_4, x_5, x_6, x_202);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_203;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_200;
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_160, 0);
lean_inc(x_204);
lean_dec(x_160);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_137);
return x_205;
}
}
}
block_210:
{
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = l_Lean_Expr_isProj(x_1);
if (x_208 == 0)
{
lean_object* x_209; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_11)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_11;
}
lean_ctor_set(x_209, 0, x_1);
lean_ctor_set(x_209, 1, x_10);
return x_209;
}
else
{
lean_dec(x_11);
x_64 = x_208;
goto block_206;
}
}
else
{
lean_dec(x_11);
x_64 = x_207;
goto block_206;
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_407 = !lean_is_exclusive(x_8);
if (x_407 == 0)
{
return x_8;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_8, 0);
x_409 = lean_ctor_get(x_8, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_8);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Expr_withAppAux___at___Lean_Meta_Grind_markNestedProofsImpl_visit_spec__3(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_markNestedProofsImpl_visit___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofsImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(64u);
x_8 = l_Lean_mkPtrMap(lean_box(0), lean_box(0), x_7);
x_9 = lean_st_mk_ref(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_Grind_markNestedProofsImpl_visit(x_1, x_10, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_dec(x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_markNestedProofsImpl(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedProofs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_markNestedProofsImpl(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
