// Lean compiler output
// Module: Lean.Meta.ExprLens
// Imports: Lean.Meta.Basic Lean.SubExpr
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Core_numBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_size___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Core_numBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__2(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_mk_string_unchecked("Invalid coordinate ", 19, 19);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked(" for ", 5, 5);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_MessageData_ofExpr(x_4);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___redArg(x_1, x_2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_10);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(1);
x_6 = lean_box(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 9, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_empty_array_with_capacity(x_1);
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_box(x_2);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_3);
x_12 = lean_expr_instantiate_rev(x_4, x_9);
lean_dec(x_9);
x_13 = lean_apply_1(x_5, x_12);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_11; uint8_t x_12; 
x_11 = lean_ptr_addr(x_1);
x_12 = lean_usize_dec_eq(x_11, x_11);
if (x_12 == 0)
{
x_6 = x_12;
goto block_10;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_4);
x_14 = lean_ptr_addr(x_5);
x_15 = lean_usize_dec_eq(x_13, x_14);
x_6 = x_15;
goto block_10;
}
block_10:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = l_Lean_Expr_app___override(x_1, x_5);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_apply_2(x_2, lean_box(0), x_3);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_box(1);
x_7 = lean_box(x_2);
x_8 = lean_box(x_3);
x_9 = lean_box(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 11, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_8);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_6);
x_11 = lean_apply_2(x_4, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_mk_empty_array_with_capacity(x_1);
x_10 = lean_array_push(x_9, x_8);
x_11 = lean_box(x_2);
x_12 = lean_box(x_3);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed), 5, 4);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_expr_instantiate_rev(x_5, x_10);
lean_dec(x_10);
x_15 = lean_apply_1(x_6, x_14);
x_16 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_box(1);
x_7 = lean_box(x_2);
x_8 = lean_box(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 10, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_7);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_6);
x_10 = lean_apply_2(x_4, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_mk_empty_array_with_capacity(x_1);
x_10 = lean_array_push(x_9, x_8);
x_11 = lean_box(x_2);
x_12 = lean_box(x_3);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed), 5, 4);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_expr_instantiate_rev(x_5, x_10);
lean_dec(x_10);
x_15 = lean_apply_1(x_6, x_14);
x_16 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_12; size_t x_17; uint8_t x_18; 
x_17 = lean_ptr_addr(x_2);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
x_12 = x_18;
goto block_16;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_7);
x_20 = lean_ptr_addr(x_8);
x_21 = lean_usize_dec_eq(x_19, x_20);
x_12 = x_21;
goto block_16;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_letE___override(x_1, x_2, x_8, x_3, x_4);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
return x_10;
}
block_16:
{
if (x_12 == 0)
{
lean_dec(x_6);
goto block_11;
}
else
{
size_t x_13; uint8_t x_14; 
x_13 = lean_ptr_addr(x_3);
x_14 = lean_usize_dec_eq(x_13, x_13);
if (x_14 == 0)
{
lean_dec(x_6);
goto block_11;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_apply_2(x_5, lean_box(0), x_6);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_ptr_addr(x_4);
x_12 = lean_ptr_addr(x_5);
x_13 = lean_usize_dec_eq(x_11, x_12);
if (x_13 == 0)
{
x_6 = x_13;
goto block_10;
}
else
{
size_t x_14; uint8_t x_15; 
x_14 = lean_ptr_addr(x_1);
x_15 = lean_usize_dec_eq(x_14, x_14);
x_6 = x_15;
goto block_10;
}
block_10:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = l_Lean_Expr_app___override(x_5, x_1);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_apply_2(x_2, lean_box(0), x_3);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 6)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; size_t x_20; size_t x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
x_20 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_21 = lean_ptr_addr(x_6);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_10);
x_12 = x_22;
goto block_19;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_24 = lean_ptr_addr(x_3);
x_25 = lean_usize_dec_eq(x_23, x_24);
x_12 = x_25;
goto block_19;
}
block_19:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = l_Lean_Expr_lam___override(x_8, x_6, x_3, x_4);
x_14 = lean_apply_2(x_5, lean_box(0), x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_11, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_16 = l_Lean_Expr_lam___override(x_8, x_6, x_3, x_4);
x_17 = lean_apply_2(x_5, lean_box(0), x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_18 = lean_apply_2(x_5, lean_box(0), x_7);
return x_18;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_26 = l_Lean_instInhabitedExpr;
x_27 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_28 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_29 = lean_unsigned_to_nat(1848u);
x_30 = lean_unsigned_to_nat(19u);
x_31 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_32 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_27, x_28, x_29, x_30, x_31);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
x_33 = l_panic___redArg(x_26, x_32);
x_34 = lean_apply_2(x_5, lean_box(0), x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; size_t x_20; size_t x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
x_20 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_21 = lean_ptr_addr(x_6);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_10);
x_12 = x_22;
goto block_19;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_24 = lean_ptr_addr(x_3);
x_25 = lean_usize_dec_eq(x_23, x_24);
x_12 = x_25;
goto block_19;
}
block_19:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = l_Lean_Expr_forallE___override(x_8, x_6, x_3, x_4);
x_14 = lean_apply_2(x_5, lean_box(0), x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_11, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_16 = l_Lean_Expr_forallE___override(x_8, x_6, x_3, x_4);
x_17 = lean_apply_2(x_5, lean_box(0), x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_18 = lean_apply_2(x_5, lean_box(0), x_7);
return x_18;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_26 = l_Lean_instInhabitedExpr;
x_27 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_28 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_29 = lean_unsigned_to_nat(1828u);
x_30 = lean_unsigned_to_nat(23u);
x_31 = lean_mk_string_unchecked("forall expected", 15, 15);
x_32 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_27, x_28, x_29, x_30, x_31);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
x_33 = l_panic___redArg(x_26, x_32);
x_34 = lean_apply_2(x_5, lean_box(0), x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_12; size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_7);
x_18 = lean_ptr_addr(x_8);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
x_12 = x_19;
goto block_16;
}
else
{
size_t x_20; uint8_t x_21; 
x_20 = lean_ptr_addr(x_2);
x_21 = lean_usize_dec_eq(x_20, x_20);
x_12 = x_21;
goto block_16;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_letE___override(x_1, x_8, x_2, x_3, x_4);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
return x_10;
}
block_16:
{
if (x_12 == 0)
{
lean_dec(x_6);
goto block_11;
}
else
{
size_t x_13; uint8_t x_14; 
x_13 = lean_ptr_addr(x_3);
x_14 = lean_usize_dec_eq(x_13, x_13);
if (x_14 == 0)
{
lean_dec(x_6);
goto block_11;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_apply_2(x_5, lean_box(0), x_6);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_dec_eq(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_8);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_dec_eq(x_6, x_18);
if (x_19 == 0)
{
if (lean_obj_tag(x_7) == 10)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(x_11, x_7, x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_21);
lean_dec(x_20);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_4, x_6, x_7);
return x_23;
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_7) == 10)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
x_26 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(x_11, x_7, x_1, x_2, x_3, x_4, x_5, x_18, x_24, x_25);
lean_dec(x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_mk_string_unchecked("Lensing on types is not supported", 33, 33);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = l_Lean_throwError___redArg(x_1, x_4, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 8:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_4);
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_7, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_box(x_17);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed), 7, 6);
lean_closure_set(x_35, 0, x_14);
lean_closure_set(x_35, 1, x_34);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_33);
lean_closure_set(x_35, 4, x_5);
lean_closure_set(x_35, 5, x_8);
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
x_38 = l_Lean_Meta_withLetDecl___redArg(x_3, x_1, x_30, x_31, x_32, x_35, x_37);
return x_38;
}
case 10:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
x_41 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(x_11, x_7, x_1, x_2, x_3, x_4, x_5, x_16, x_39, x_40);
lean_dec(x_39);
return x_41;
}
default: 
{
lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_42 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_4, x_16, x_7);
return x_42;
}
}
}
}
else
{
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 5:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_44);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed), 5, 4);
lean_closure_set(x_45, 0, x_43);
lean_closure_set(x_45, 1, x_10);
lean_closure_set(x_45, 2, x_7);
lean_closure_set(x_45, 3, x_44);
x_46 = lean_apply_1(x_5, x_44);
x_47 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_46, x_45);
return x_47;
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_48 = lean_ctor_get(x_7, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_7, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_52 = lean_box(x_13);
x_53 = lean_box(x_15);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed), 8, 7);
lean_closure_set(x_54, 0, x_14);
lean_closure_set(x_54, 1, x_52);
lean_closure_set(x_54, 2, x_53);
lean_closure_set(x_54, 3, x_2);
lean_closure_set(x_54, 4, x_50);
lean_closure_set(x_54, 5, x_5);
lean_closure_set(x_54, 6, x_8);
x_55 = lean_box(0);
x_56 = lean_unbox(x_55);
x_57 = l_Lean_Meta_withLocalDecl___redArg(x_3, x_1, x_48, x_51, x_49, x_54, x_56);
return x_57;
}
case 7:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_58 = lean_ctor_get(x_7, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_7, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_62 = lean_box(x_13);
x_63 = lean_box(x_15);
x_64 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed), 8, 7);
lean_closure_set(x_64, 0, x_14);
lean_closure_set(x_64, 1, x_62);
lean_closure_set(x_64, 2, x_63);
lean_closure_set(x_64, 3, x_2);
lean_closure_set(x_64, 4, x_60);
lean_closure_set(x_64, 5, x_5);
lean_closure_set(x_64, 6, x_8);
x_65 = lean_box(0);
x_66 = lean_unbox(x_65);
x_67 = l_Lean_Meta_withLocalDecl___redArg(x_3, x_1, x_58, x_61, x_59, x_64, x_66);
return x_67;
}
case 8:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_7, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_7, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 3);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_7, sizeof(void*)*4 + 8);
x_73 = lean_box(x_72);
lean_inc(x_70);
x_74 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed), 8, 7);
lean_closure_set(x_74, 0, x_68);
lean_closure_set(x_74, 1, x_69);
lean_closure_set(x_74, 2, x_71);
lean_closure_set(x_74, 3, x_73);
lean_closure_set(x_74, 4, x_10);
lean_closure_set(x_74, 5, x_7);
lean_closure_set(x_74, 6, x_70);
x_75 = lean_apply_1(x_5, x_70);
x_76 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_75, x_74);
return x_76;
}
case 10:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_10);
lean_dec(x_8);
x_77 = lean_ctor_get(x_7, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
x_79 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(x_11, x_7, x_1, x_2, x_3, x_4, x_5, x_14, x_77, x_78);
lean_dec(x_77);
return x_79;
}
default: 
{
lean_object* x_80; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_80 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_4, x_14, x_7);
return x_80;
}
}
}
}
else
{
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 5:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_ctor_get(x_7, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_7, 1);
lean_inc(x_82);
lean_inc(x_81);
x_83 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed), 5, 4);
lean_closure_set(x_83, 0, x_82);
lean_closure_set(x_83, 1, x_10);
lean_closure_set(x_83, 2, x_7);
lean_closure_set(x_83, 3, x_81);
x_84 = lean_apply_1(x_5, x_81);
x_85 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_84, x_83);
return x_85;
}
case 6:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_ctor_get(x_7, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_7, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_7, 2);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_90 = lean_box(x_89);
lean_inc(x_87);
x_91 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__11___boxed), 6, 5);
lean_closure_set(x_91, 0, x_86);
lean_closure_set(x_91, 1, x_87);
lean_closure_set(x_91, 2, x_88);
lean_closure_set(x_91, 3, x_90);
lean_closure_set(x_91, 4, x_10);
x_92 = lean_apply_1(x_5, x_87);
x_93 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_92, x_91);
return x_93;
}
case 7:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_7, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_7, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_7, 2);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_98 = lean_box(x_97);
lean_inc(x_95);
x_99 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__12___boxed), 6, 5);
lean_closure_set(x_99, 0, x_94);
lean_closure_set(x_99, 1, x_95);
lean_closure_set(x_99, 2, x_96);
lean_closure_set(x_99, 3, x_98);
lean_closure_set(x_99, 4, x_10);
x_100 = lean_apply_1(x_5, x_95);
x_101 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_100, x_99);
return x_101;
}
case 8:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_7, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_7, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_7, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_7, 3);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_7, sizeof(void*)*4 + 8);
x_107 = lean_box(x_106);
lean_inc(x_103);
x_108 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__13___boxed), 8, 7);
lean_closure_set(x_108, 0, x_102);
lean_closure_set(x_108, 1, x_104);
lean_closure_set(x_108, 2, x_105);
lean_closure_set(x_108, 3, x_107);
lean_closure_set(x_108, 4, x_10);
lean_closure_set(x_108, 5, x_7);
lean_closure_set(x_108, 6, x_103);
x_109 = lean_apply_1(x_5, x_103);
x_110 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_109, x_108);
return x_110;
}
case 10:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_10);
lean_dec(x_8);
x_111 = lean_ctor_get(x_7, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_7, 1);
lean_inc(x_112);
x_113 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(x_11, x_7, x_1, x_2, x_3, x_4, x_5, x_12, x_111, x_112);
lean_dec(x_111);
return x_113;
}
case 11:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_7, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_11, 0);
lean_inc(x_115);
lean_dec(x_11);
x_116 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(x_116, 0, x_7);
x_117 = lean_apply_1(x_5, x_114);
x_118 = lean_apply_4(x_115, lean_box(0), lean_box(0), x_116, x_117);
return x_118;
}
default: 
{
lean_object* x_119; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_119 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_4, x_12, x_7);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__2(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__6(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__7(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__8(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__9(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__11(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__12(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__13(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_apply_1(x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg), 7, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_10);
x_12 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg(x_1, x_2, x_3, x_4, x_11, x_9, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_SubExpr_Pos_toArray(x_6);
x_9 = lean_array_to_list(x_8);
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensAux___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_replaceSubexpr___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_replaceSubexpr___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_replaceSubexpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_replaceSubexpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_push(x_1, x_4);
x_6 = lean_apply_2(x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_push(x_1, x_4);
x_6 = lean_apply_2(x_2, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_expr_instantiate_rev(x_6, x_1);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_withLocalDecl___redArg(x_3, x_4, x_5, x_8, x_10, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_dec_eq(x_6, x_14);
if (x_15 == 0)
{
if (lean_obj_tag(x_7) == 10)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_3, x_6, x_7);
return x_18;
}
}
else
{
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 3);
lean_inc(x_22);
lean_dec(x_7);
lean_inc(x_5);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__1), 4, 3);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_4);
lean_closure_set(x_23, 2, x_22);
x_24 = lean_expr_instantiate_rev(x_20, x_5);
lean_dec(x_20);
x_25 = lean_expr_instantiate_rev(x_21, x_5);
lean_dec(x_5);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Meta_withLetDecl___redArg(x_2, x_1, x_19, x_24, x_25, x_23, x_27);
return x_28;
}
case 10:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_dec(x_7);
x_6 = x_14;
x_7 = x_29;
goto _start;
}
default: 
{
lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_3, x_14, x_7);
return x_31;
}
}
}
}
else
{
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 5:
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_apply_2(x_4, x_5, x_32);
return x_33;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
lean_dec(x_3);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_7, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_38 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__2(x_5, x_4, x_2, x_1, x_34, x_35, x_36, x_37);
lean_dec(x_35);
return x_38;
}
case 7:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
lean_dec(x_3);
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_43 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__2(x_5, x_4, x_2, x_1, x_39, x_40, x_41, x_42);
lean_dec(x_40);
return x_43;
}
case 8:
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_7, 2);
lean_inc(x_44);
lean_dec(x_7);
x_45 = lean_apply_2(x_4, x_5, x_44);
return x_45;
}
case 10:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_dec(x_7);
x_6 = x_12;
x_7 = x_46;
goto _start;
}
default: 
{
lean_object* x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_48 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_3, x_12, x_7);
return x_48;
}
}
}
}
else
{
lean_dec(x_6);
switch (lean_obj_tag(x_7)) {
case 5:
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_7, 0);
lean_inc(x_49);
lean_dec(x_7);
x_50 = lean_apply_2(x_4, x_5, x_49);
return x_50;
}
case 6:
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_dec(x_7);
x_52 = lean_apply_2(x_4, x_5, x_51);
return x_52;
}
case 7:
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_dec(x_7);
x_54 = lean_apply_2(x_4, x_5, x_53);
return x_54;
}
case 8:
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_dec(x_7);
x_56 = lean_apply_2(x_4, x_5, x_55);
return x_56;
}
case 10:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_dec(x_7);
x_6 = x_10;
x_7 = x_57;
goto _start;
}
case 11:
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_7, 2);
lean_inc(x_59);
lean_dec(x_7);
x_60 = lean_apply_2(x_4, x_5, x_59);
return x_60;
}
default: 
{
lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_61 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_lensCoord___redArg___lam__0(x_1, x_3, x_10, x_7);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_62 = lean_mk_string_unchecked("Internal: Types should be handled by viewAux", 44, 44);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = l_Lean_throwError___redArg(x_1, x_3, x_63);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(x_2, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Array_append(lean_box(0), x_1, x_3);
x_6 = lean_apply_2(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_expr_instantiate_rev(x_8, x_6);
lean_dec(x_8);
x_10 = lean_apply_2(x_5, x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_dec_eq(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__0), 8, 6);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_13);
x_17 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(x_1, x_3, x_4, x_16, x_6, x_12, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_inc(x_6);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_5);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__2), 7, 6);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_18);
lean_closure_set(x_19, 5, x_13);
x_20 = lean_expr_instantiate_rev(x_8, x_6);
lean_dec(x_6);
lean_dec(x_8);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_apply_2(x_2, lean_box(0), x_21);
x_23 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_22, x_19);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = l_Lean_SubExpr_Pos_toArray(x_6);
x_11 = lean_array_to_list(x_10);
x_12 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewAux___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_viewSubexpr___redArg(x_2, x_3, x_4, x_5, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_viewSubexpr___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_viewSubexpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_viewSubexpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg), 9, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_10);
lean_closure_set(x_11, 6, x_6);
x_12 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_viewCoordAux___redArg(x_1, x_3, x_4, x_11, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Array_append(lean_box(0), x_1, x_3);
x_8 = lean_apply_4(x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_6, x_10, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__2), 8, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_13);
x_15 = lean_apply_4(x_7, x_8, x_9, x_10, x_11);
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_dec_eq(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_9);
lean_inc(x_14);
lean_inc(x_8);
lean_inc(x_5);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__0), 10, 9);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_15);
lean_closure_set(x_18, 6, x_8);
lean_closure_set(x_18, 7, x_14);
lean_closure_set(x_18, 8, x_9);
x_19 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
x_20 = lean_apply_4(x_5, x_8, x_19, x_14, x_6);
x_21 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_8);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed), 6, 2);
lean_closure_set(x_22, 0, x_8);
lean_closure_set(x_22, 1, x_5);
x_23 = lean_expr_instantiate_rev(x_9, x_8);
lean_dec(x_9);
lean_inc(x_13);
lean_inc(x_23);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__3), 13, 12);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_3);
lean_closure_set(x_24, 3, x_4);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_15);
lean_closure_set(x_24, 6, x_5);
lean_closure_set(x_24, 7, x_8);
lean_closure_set(x_24, 8, x_23);
lean_closure_set(x_24, 9, x_16);
lean_closure_set(x_24, 10, x_6);
lean_closure_set(x_24, 11, x_13);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_25, 0, x_23);
x_26 = lean_apply_2(x_2, lean_box(0), x_25);
x_27 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_26, x_24);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_SubExpr_Pos_toArray(x_7);
x_10 = lean_array_to_list(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = l___private_Lean_Meta_ExprLens_0__Lean_Meta_foldAncestorsAux___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_12, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_foldAncestors___redArg(x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_foldAncestors___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_foldAncestors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_foldAncestors(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_mk_string_unchecked("Can't viewRaw the type of ", 26, 26);
x_5 = l_Lean_stringToMessageData(x_4);
lean_dec(x_4);
x_6 = l_Lean_MessageData_ofExpr(x_3);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_throwError___redArg(x_1, x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_mk_string_unchecked("Bad coordinate ", 15, 15);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked(" for ", 5, 5);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_MessageData_ofExpr(x_3);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___redArg(x_1, x_2, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_bvar___override(x_5);
x_9 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l_Lean_Expr_bvar___override(x_5);
x_11 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_10);
return x_11;
}
}
case 1:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_dec_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_fvar___override(x_12);
x_16 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_15, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = l_Lean_Expr_fvar___override(x_12);
x_18 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_17);
return x_18;
}
}
case 2:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_dec_eq(x_4, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_mvar___override(x_19);
x_23 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_22, x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_24 = l_Lean_Expr_mvar___override(x_19);
x_25 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_24);
return x_25;
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_dec_eq(x_4, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_sort___override(x_26);
x_30 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_29, x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_31 = l_Lean_Expr_sort___override(x_26);
x_32 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_31);
return x_32;
}
}
case 4:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_dec_eq(x_4, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Expr_const___override(x_33, x_34);
x_38 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_37, x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
x_39 = l_Lean_Expr_const___override(x_33, x_34);
x_40 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_39);
return x_40;
}
}
case 5:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_dec_eq(x_4, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_eq(x_4, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_dec_eq(x_4, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
x_51 = l_Lean_Expr_app___override(x_43, x_44);
x_52 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_51, x_4);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_apply_2(x_42, lean_box(0), x_44);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_44);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_apply_2(x_42, lean_box(0), x_43);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_42);
lean_dec(x_4);
x_55 = l_Lean_Expr_app___override(x_43, x_44);
x_56 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_55);
return x_56;
}
}
case 6:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 2);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_dec_eq(x_4, x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_4, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_dec_eq(x_4, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_58);
x_69 = l_Lean_Expr_lam___override(x_59, x_60, x_61, x_62);
x_70 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_69, x_4);
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_apply_2(x_58, lean_box(0), x_61);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_apply_2(x_58, lean_box(0), x_60);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_58);
lean_dec(x_4);
x_73 = l_Lean_Expr_lam___override(x_59, x_60, x_61, x_62);
x_74 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_73);
return x_74;
}
}
case 7:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 2);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_dec_eq(x_4, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_nat_dec_eq(x_4, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_dec_eq(x_4, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_76);
x_87 = l_Lean_Expr_forallE___override(x_77, x_78, x_79, x_80);
x_88 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_87, x_4);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_apply_2(x_76, lean_box(0), x_79);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_apply_2(x_76, lean_box(0), x_78);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
lean_dec(x_4);
x_91 = l_Lean_Expr_forallE___override(x_77, x_78, x_79, x_80);
x_92 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_91);
return x_92;
}
}
case 8:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; uint8_t x_101; 
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_3, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 3);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_dec(x_3);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_dec_eq(x_4, x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_nat_dec_eq(x_4, x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_dec_eq(x_4, x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_unsigned_to_nat(2u);
x_107 = lean_nat_dec_eq(x_4, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_94);
x_108 = l_Lean_Expr_letE___override(x_95, x_96, x_97, x_98, x_99);
x_109 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_108, x_4);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_apply_2(x_94, lean_box(0), x_98);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_apply_2(x_94, lean_box(0), x_97);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_apply_2(x_94, lean_box(0), x_96);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_94);
lean_dec(x_4);
x_113 = l_Lean_Expr_letE___override(x_95, x_96, x_97, x_98, x_99);
x_114 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_113);
return x_114;
}
}
case 9:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_3, 0);
lean_inc(x_115);
lean_dec(x_3);
x_116 = lean_unsigned_to_nat(3u);
x_117 = lean_nat_dec_eq(x_4, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_Expr_lit___override(x_115);
x_119 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_118, x_4);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_4);
x_120 = l_Lean_Expr_lit___override(x_115);
x_121 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_120);
return x_121;
}
}
case 10:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_3, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_3, 1);
lean_inc(x_123);
lean_dec(x_3);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_dec_eq(x_4, x_124);
if (x_125 == 0)
{
lean_dec(x_122);
x_3 = x_123;
goto _start;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_4);
x_127 = l_Lean_Expr_mdata___override(x_122, x_123);
x_128 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_127);
return x_128;
}
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_ctor_get(x_3, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 2);
lean_inc(x_133);
lean_dec(x_3);
x_134 = lean_unsigned_to_nat(3u);
x_135 = lean_nat_dec_eq(x_4, x_134);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_eq(x_4, x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_130);
x_138 = l_Lean_Expr_proj___override(x_131, x_132, x_133);
x_139 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__1(x_1, x_2, x_138, x_4);
return x_139;
}
else
{
lean_object* x_140; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_apply_2(x_130, lean_box(0), x_133);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_130);
lean_dec(x_4);
x_141 = l_Lean_Expr_proj___override(x_131, x_132, x_133);
x_142 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg___lam__0(x_1, x_2, x_141);
return x_142;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw), 5, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Lean_SubExpr_Pos_foldlM___redArg(x_1, x_5, x_4, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewSubexpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_viewSubexpr___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
}
}
else
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_17 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___lam__0(x_13, x_14, x_15, x_16);
lean_dec(x_15);
return x_17;
}
case 7:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___lam__0(x_18, x_19, x_20, x_21);
lean_dec(x_20);
return x_22;
}
default: 
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_box(0);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___lam__0(x_1, x_2, x_3, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_10; 
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewBindersCoord(x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
x_6 = x_4;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_push(x_4, x_11);
x_6 = x_12;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_8);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_7);
x_10 = l___private_Lean_Meta_ExprLens_0__Lean_Core_viewCoordRaw___redArg(x_2, x_3, x_8, x_6);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__1), 6, 4);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Core_viewBinders___redArg___lam__2), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = l_Lean_SubExpr_Pos_foldlM___redArg(x_1, x_8, x_12, x_3);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_viewBinders___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_viewBinders___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_viewBinders___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_numBinders___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Array_size___boxed), 2, 1);
lean_closure_set(x_8, 0, lean_box(0));
x_9 = l_Lean_Core_viewBinders___redArg(x_1, x_2, x_3, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_numBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_numBinders___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_SubExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ExprLens(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_SubExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
