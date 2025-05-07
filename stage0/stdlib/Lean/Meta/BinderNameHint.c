// Lean compiler output
// Module: Lean.Meta.BinderNameHint
// Imports: Lean.Util.FindExpr Lean.Meta.Basic Init.BinderNameHint
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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_enterScope(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__3(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__0(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___lam__0___boxed(lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__8(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__6(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__5(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("binderNameHint", 14, 14);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Expr_isConstOf(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasBinderNameHint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_hasBinderNameHint___lam__0___boxed), 1, 0);
x_3 = lean_find_expr(x_2, x_1);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasBinderNameHint___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasBinderNameHint___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasBinderNameHint(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_enterScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Array_instInhabited(lean_box(0));
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_panic_fn(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("Lean.Meta.BinderNameHint", 24, 24);
x_6 = lean_mk_string_unchecked("_private.Lean.Meta.BinderNameHint.0.Lean.exitScope", 50, 50);
x_7 = lean_unsigned_to_nat(24u);
x_8 = lean_unsigned_to_nat(4u);
x_9 = lean_mk_string_unchecked("assertion violation: xs.size > 0\n    ", 37, 37);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_exitScope_spec__0(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = l_Array_back_x21(lean_box(0), x_12, x_1);
x_14 = lean_array_pop(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("Lean.Meta.BinderNameHint", 24, 24);
x_7 = lean_mk_string_unchecked("_private.Lean.Meta.BinderNameHint.0.Lean.rememberName", 53, 53);
x_8 = lean_unsigned_to_nat(28u);
x_9 = lean_unsigned_to_nat(4u);
x_10 = lean_mk_string_unchecked("assertion violation: xs.size > bidx\n    ", 40, 40);
x_11 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_12 = l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_rememberName_spec__0(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_nat_sub(x_4, x_1);
lean_dec(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_array_set(x_3, x_15, x_2);
lean_dec(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_2);
x_8 = lean_mk_string_unchecked("Lean.Meta.BinderNameHint", 24, 24);
x_9 = lean_mk_string_unchecked("_private.Lean.Meta.BinderNameHint.0.Lean.makeFresh", 50, 50);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_unsigned_to_nat(4u);
x_12 = lean_mk_string_unchecked("assertion violation: xs.size > bidx\n    ", 40, 40);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at_____private_Lean_Meta_BinderNameHint_0__Lean_makeFresh_spec__0(x_13, x_3, x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_box(0);
x_16 = lean_nat_sub(x_6, x_1);
lean_dec(x_6);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_array_get(x_15, x_2, x_18);
x_20 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_19, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_array_set(x_2, x_18, x_22);
lean_dec(x_18);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_array_set(x_2, x_18, x_24);
lean_dec(x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_BinderNameHint_0__Lean_makeFresh(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_apply_1(x_4, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__2), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, x_6, x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__3), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__5), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, x_6, x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__6), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__8), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__1), 5, 0);
x_8 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__4), 5, 0);
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__7), 5, 0);
x_10 = lean_alloc_closure((void*)(l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0___lam__9), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_13 = l_instMonadEIO(lean_box(0));
x_14 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, lean_box(0));
lean_closure_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
lean_inc(x_30);
x_33 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, lean_box(0));
lean_closure_set(x_33, 2, x_30);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_8);
lean_ctor_set(x_34, 3, x_9);
lean_ctor_set(x_34, 4, x_10);
x_35 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_35, 0, lean_box(0));
lean_closure_set(x_35, 1, lean_box(0));
lean_closure_set(x_35, 2, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_36);
x_38 = l_Lean_instInhabitedExpr;
x_39 = l_instInhabitedOfMonad___redArg(x_37, x_38);
x_40 = lean_panic_fn(x_39, x_1);
x_41 = lean_apply_5(x_40, x_2, x_3, x_4, x_5, x_6);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_6(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_headBeta(x_1);
x_14 = lean_apply_7(x_2, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(x_2, x_3, x_8);
x_14 = lean_apply_6(x_1, x_12, x_7, x_13, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_2);
x_12 = lean_mk_string_unchecked("Lean.Meta.BinderNameHint", 24, 24);
x_13 = lean_mk_string_unchecked("Lean.Expr.resolveBinderNameHint.go", 34, 34);
x_14 = lean_unsigned_to_nat(70u);
x_15 = lean_unsigned_to_nat(10u);
x_16 = lean_mk_string_unchecked("assertion violation: xs.size > bidx\n          ", 46, 46);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Expr_resolveBinderNameHint_go_spec__0(x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_box(0);
x_20 = lean_nat_sub(x_10, x_3);
lean_dec(x_10);
x_21 = lean_nat_sub(x_20, x_1);
lean_dec(x_20);
x_22 = lean_array_get(x_19, x_6, x_21);
lean_dec(x_21);
x_23 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_22, x_7, x_8, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = l___private_Lean_Meta_BinderNameHint_0__Lean_rememberName(x_3, x_24, x_6);
x_28 = lean_apply_6(x_2, x_26, x_5, x_27, x_7, x_8, x_25);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_95; lean_object* x_100; uint8_t x_101; 
x_100 = lean_st_ref_get(x_2, x_6);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint64_t x_108; lean_object* x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; lean_object* x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; size_t x_117; size_t x_118; lean_object* x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; lean_object* x_124; 
x_104 = lean_ctor_get(x_100, 1);
x_105 = lean_ctor_get(x_102, 1);
x_106 = lean_ctor_get(x_102, 0);
lean_dec(x_106);
x_107 = lean_array_get_size(x_105);
x_108 = l_Lean_Expr_hash(x_1);
x_109 = lean_unsigned_to_nat(32u);
x_110 = lean_uint64_of_nat(x_109);
x_111 = lean_uint64_shift_right(x_108, x_110);
x_112 = lean_uint64_xor(x_108, x_111);
x_113 = lean_unsigned_to_nat(16u);
x_114 = lean_uint64_of_nat(x_113);
x_115 = lean_uint64_shift_right(x_112, x_114);
x_116 = lean_uint64_xor(x_112, x_115);
x_117 = lean_uint64_to_usize(x_116);
x_118 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_usize_of_nat(x_119);
x_121 = lean_usize_sub(x_118, x_120);
x_122 = lean_usize_land(x_117, x_121);
x_123 = lean_array_uget(x_105, x_122);
lean_dec(x_105);
x_124 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_1, x_123);
lean_dec(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_free_object(x_100);
x_125 = lean_mk_string_unchecked("binderNameHint", 14, 14);
x_126 = l_Lean_Name_mkStr1(x_125);
x_127 = lean_unsigned_to_nat(6u);
x_128 = l_Lean_Expr_isAppOfArity(x_1, x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_free_object(x_102);
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_1, 1);
lean_inc(x_130);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_129);
x_131 = l_Lean_Expr_resolveBinderNameHint_go(x_129, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
lean_inc(x_2);
lean_inc(x_130);
x_136 = l_Lean_Expr_resolveBinderNameHint_go(x_130, x_2, x_135, x_4, x_5, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_145; size_t x_148; size_t x_149; uint8_t x_150; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_141 = x_137;
} else {
 lean_dec_ref(x_137);
 x_141 = lean_box(0);
}
x_148 = lean_ptr_addr(x_129);
lean_dec(x_129);
x_149 = lean_ptr_addr(x_134);
x_150 = lean_usize_dec_eq(x_148, x_149);
if (x_150 == 0)
{
lean_dec(x_130);
x_145 = x_150;
goto block_147;
}
else
{
size_t x_151; size_t x_152; uint8_t x_153; 
x_151 = lean_ptr_addr(x_130);
lean_dec(x_130);
x_152 = lean_ptr_addr(x_139);
x_153 = lean_usize_dec_eq(x_151, x_152);
x_145 = x_153;
goto block_147;
}
block_144:
{
lean_object* x_143; 
lean_inc(x_142);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
x_16 = x_143;
x_17 = x_142;
x_18 = x_138;
goto block_94;
}
block_147:
{
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = l_Lean_Expr_app___override(x_134, x_139);
x_142 = x_146;
goto block_144;
}
else
{
lean_dec(x_139);
lean_dec(x_134);
lean_inc(x_1);
x_142 = x_1;
goto block_144;
}
}
}
else
{
lean_dec(x_134);
lean_dec(x_130);
lean_dec(x_129);
x_95 = x_136;
goto block_99;
}
}
else
{
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_131;
goto block_99;
}
}
case 6:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
lean_free_object(x_102);
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_1, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_1, 2);
lean_inc(x_156);
x_157 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_158 = l_Lean_Expr_resolveBinderNameHint_go(x_155, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
x_163 = lean_array_push(x_162, x_154);
lean_inc(x_2);
x_164 = l_Lean_Expr_resolveBinderNameHint_go(x_156, x_2, x_163, x_4, x_5, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_168);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = l_Lean_Expr_lam___override(x_171, x_161, x_167, x_157);
lean_inc(x_172);
lean_ctor_set(x_169, 0, x_172);
x_16 = x_169;
x_17 = x_172;
x_18 = x_166;
goto block_94;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_169, 0);
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_169);
x_175 = l_Lean_Expr_lam___override(x_173, x_161, x_167, x_157);
lean_inc(x_175);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_16 = x_176;
x_17 = x_175;
x_18 = x_166;
goto block_94;
}
}
else
{
lean_dec(x_161);
x_95 = x_164;
goto block_99;
}
}
else
{
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_158;
goto block_99;
}
}
case 7:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; 
lean_free_object(x_102);
x_177 = lean_ctor_get(x_1, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_1, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 2);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_181 = l_Lean_Expr_resolveBinderNameHint_go(x_178, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_182, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_array_push(x_185, x_177);
lean_inc(x_2);
x_187 = l_Lean_Expr_resolveBinderNameHint_go(x_179, x_2, x_186, x_4, x_5, x_183);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_191);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = l_Lean_Expr_forallE___override(x_194, x_184, x_190, x_180);
lean_inc(x_195);
lean_ctor_set(x_192, 0, x_195);
x_16 = x_192;
x_17 = x_195;
x_18 = x_189;
goto block_94;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_192, 0);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_192);
x_198 = l_Lean_Expr_forallE___override(x_196, x_184, x_190, x_180);
lean_inc(x_198);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_16 = x_199;
x_17 = x_198;
x_18 = x_189;
goto block_94;
}
}
else
{
lean_dec(x_184);
x_95 = x_187;
goto block_99;
}
}
else
{
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_181;
goto block_99;
}
}
case 8:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; 
lean_free_object(x_102);
x_200 = lean_ctor_get(x_1, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_1, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_1, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_1, 3);
lean_inc(x_203);
x_204 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_205 = l_Lean_Expr_resolveBinderNameHint_go(x_201, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_210 = l_Lean_Expr_resolveBinderNameHint_go(x_202, x_2, x_209, x_4, x_5, x_207);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_array_push(x_214, x_200);
lean_inc(x_2);
x_216 = l_Lean_Expr_resolveBinderNameHint_go(x_203, x_2, x_215, x_4, x_5, x_212);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_220);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = l_Lean_Expr_letE___override(x_223, x_208, x_213, x_219, x_204);
lean_inc(x_224);
lean_ctor_set(x_221, 0, x_224);
x_16 = x_221;
x_17 = x_224;
x_18 = x_218;
goto block_94;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_221, 0);
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_221);
x_227 = l_Lean_Expr_letE___override(x_225, x_208, x_213, x_219, x_204);
lean_inc(x_227);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_16 = x_228;
x_17 = x_227;
x_18 = x_218;
goto block_94;
}
}
else
{
lean_dec(x_213);
lean_dec(x_208);
x_95 = x_216;
goto block_99;
}
}
else
{
lean_dec(x_208);
lean_dec(x_203);
lean_dec(x_200);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_210;
goto block_99;
}
}
else
{
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_205;
goto block_99;
}
}
case 10:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_free_object(x_102);
x_229 = lean_ctor_get(x_1, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_1, 1);
lean_inc(x_230);
lean_inc(x_2);
lean_inc(x_230);
x_231 = l_Lean_Expr_resolveBinderNameHint_go(x_230, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; size_t x_240; size_t x_241; uint8_t x_242; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_236 = x_232;
} else {
 lean_dec_ref(x_232);
 x_236 = lean_box(0);
}
x_240 = lean_ptr_addr(x_230);
lean_dec(x_230);
x_241 = lean_ptr_addr(x_234);
x_242 = lean_usize_dec_eq(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; 
x_243 = l_Lean_Expr_mdata___override(x_229, x_234);
x_237 = x_243;
goto block_239;
}
else
{
lean_dec(x_234);
lean_dec(x_229);
lean_inc(x_1);
x_237 = x_1;
goto block_239;
}
block_239:
{
lean_object* x_238; 
lean_inc(x_237);
if (lean_is_scalar(x_236)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_236;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
x_16 = x_238;
x_17 = x_237;
x_18 = x_233;
goto block_94;
}
}
else
{
lean_dec(x_230);
lean_dec(x_229);
x_95 = x_231;
goto block_99;
}
}
case 11:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_free_object(x_102);
x_244 = lean_ctor_get(x_1, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_1, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_1, 2);
lean_inc(x_246);
lean_inc(x_2);
lean_inc(x_246);
x_247 = l_Lean_Expr_resolveBinderNameHint_go(x_246, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; size_t x_256; size_t x_257; uint8_t x_258; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
x_256 = lean_ptr_addr(x_246);
lean_dec(x_246);
x_257 = lean_ptr_addr(x_250);
x_258 = lean_usize_dec_eq(x_256, x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = l_Lean_Expr_proj___override(x_244, x_245, x_250);
x_253 = x_259;
goto block_255;
}
else
{
lean_dec(x_250);
lean_dec(x_245);
lean_dec(x_244);
lean_inc(x_1);
x_253 = x_1;
goto block_255;
}
block_255:
{
lean_object* x_254; 
lean_inc(x_253);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
x_16 = x_254;
x_17 = x_253;
x_18 = x_249;
goto block_94;
}
}
else
{
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_95 = x_247;
goto block_99;
}
}
default: 
{
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_1);
lean_ctor_set(x_102, 1, x_3);
lean_ctor_set(x_102, 0, x_1);
lean_inc(x_1);
x_16 = x_102;
x_17 = x_1;
x_18 = x_104;
goto block_94;
}
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_free_object(x_102);
x_260 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_261 = l_Lean_Expr_resolveBinderNameHint_go(x_260, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = l_Lean_Expr_appFn_x21(x_1);
x_267 = l_Lean_Expr_appFn_x21(x_266);
x_268 = lean_alloc_closure((void*)(l_Lean_Expr_resolveBinderNameHint_go___lam__0___boxed), 7, 1);
lean_closure_set(x_268, 0, x_264);
lean_inc(x_268);
x_269 = lean_alloc_closure((void*)(l_Lean_Expr_resolveBinderNameHint_go___lam__1___boxed), 8, 1);
lean_closure_set(x_269, 0, x_268);
x_270 = l_Lean_Expr_appArg_x21(x_267);
lean_dec(x_267);
x_271 = l_Lean_Expr_appArg_x21(x_266);
lean_dec(x_266);
switch (lean_obj_tag(x_270)) {
case 0:
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_Lean_Expr_headBeta(x_271);
switch (lean_obj_tag(x_273)) {
case 0:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec(x_273);
x_275 = l_Lean_Expr_bvar___override(x_274);
lean_inc(x_2);
x_276 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_275, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_275);
lean_dec(x_272);
x_95 = x_276;
goto block_99;
}
case 1:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
lean_dec(x_273);
x_278 = l_Lean_Expr_fvar___override(x_277);
lean_inc(x_2);
x_279 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_278, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_278);
lean_dec(x_272);
x_95 = x_279;
goto block_99;
}
case 2:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_273, 0);
lean_inc(x_280);
lean_dec(x_273);
x_281 = l_Lean_Expr_mvar___override(x_280);
lean_inc(x_2);
x_282 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_281, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_281);
lean_dec(x_272);
x_95 = x_282;
goto block_99;
}
case 3:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_273, 0);
lean_inc(x_283);
lean_dec(x_273);
x_284 = l_Lean_Expr_sort___override(x_283);
lean_inc(x_2);
x_285 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_284, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_284);
lean_dec(x_272);
x_95 = x_285;
goto block_99;
}
case 4:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_273, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_273, 1);
lean_inc(x_287);
lean_dec(x_273);
x_288 = l_Lean_Expr_const___override(x_286, x_287);
lean_inc(x_2);
x_289 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_288, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_288);
lean_dec(x_272);
x_95 = x_289;
goto block_99;
}
case 5:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_273, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_273, 1);
lean_inc(x_291);
lean_dec(x_273);
x_292 = l_Lean_Expr_app___override(x_290, x_291);
lean_inc(x_2);
x_293 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_292, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_292);
lean_dec(x_272);
x_95 = x_293;
goto block_99;
}
case 8:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; 
x_294 = lean_ctor_get(x_273, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_273, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_273, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_273, 3);
lean_inc(x_297);
x_298 = lean_ctor_get_uint8(x_273, sizeof(void*)*4 + 8);
lean_dec(x_273);
x_299 = l_Lean_Expr_letE___override(x_294, x_295, x_296, x_297, x_298);
lean_inc(x_2);
x_300 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_299, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_299);
lean_dec(x_272);
x_95 = x_300;
goto block_99;
}
case 9:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_273, 0);
lean_inc(x_301);
lean_dec(x_273);
x_302 = l_Lean_Expr_lit___override(x_301);
lean_inc(x_2);
x_303 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_302, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_302);
lean_dec(x_272);
x_95 = x_303;
goto block_99;
}
case 10:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_273, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_273, 1);
lean_inc(x_305);
lean_dec(x_273);
x_306 = l_Lean_Expr_mdata___override(x_304, x_305);
lean_inc(x_2);
x_307 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_306, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_306);
lean_dec(x_272);
x_95 = x_307;
goto block_99;
}
case 11:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_ctor_get(x_273, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_273, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_273, 2);
lean_inc(x_310);
lean_dec(x_273);
x_311 = l_Lean_Expr_proj___override(x_308, x_309, x_310);
lean_inc(x_2);
x_312 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_119, x_268, x_272, x_311, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_311);
lean_dec(x_272);
x_95 = x_312;
goto block_99;
}
default: 
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; 
x_313 = lean_ctor_get(x_273, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_273, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_273, 2);
lean_inc(x_315);
x_316 = lean_ctor_get_uint8(x_273, sizeof(void*)*3 + 8);
lean_dec(x_273);
lean_inc(x_2);
x_317 = l_Lean_Expr_resolveBinderNameHint_go___lam__3(x_268, x_272, x_313, x_314, x_315, x_316, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_272);
x_95 = x_317;
goto block_99;
}
}
}
case 6:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
lean_dec(x_268);
x_318 = lean_ctor_get(x_270, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_270, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_270, 2);
lean_inc(x_320);
x_321 = lean_ctor_get_uint8(x_270, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_322 = l_Lean_Expr_resolveBinderNameHint_go___lam__2(x_271, x_269, x_270, x_318, x_319, x_320, x_321, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
x_95 = x_322;
goto block_99;
}
case 7:
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; 
lean_dec(x_268);
x_323 = lean_ctor_get(x_270, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_270, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_270, 2);
lean_inc(x_325);
x_326 = lean_ctor_get_uint8(x_270, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_327 = l_Lean_Expr_resolveBinderNameHint_go___lam__2(x_271, x_269, x_270, x_323, x_324, x_325, x_326, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
x_95 = x_327;
goto block_99;
}
default: 
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_269);
x_328 = l_Lean_Expr_headBeta(x_271);
lean_inc(x_2);
x_329 = l_Lean_Expr_resolveBinderNameHint_go___lam__1(x_268, x_270, x_328, x_2, x_265, x_4, x_5, x_263);
lean_dec(x_328);
lean_dec(x_270);
x_95 = x_329;
goto block_99;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_261;
goto block_99;
}
}
}
else
{
lean_object* x_330; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_330 = lean_ctor_get(x_124, 0);
lean_inc(x_330);
lean_dec(x_124);
lean_ctor_set(x_102, 1, x_3);
lean_ctor_set(x_102, 0, x_330);
return x_100;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; uint64_t x_334; lean_object* x_335; uint64_t x_336; uint64_t x_337; uint64_t x_338; lean_object* x_339; uint64_t x_340; uint64_t x_341; uint64_t x_342; size_t x_343; size_t x_344; lean_object* x_345; size_t x_346; size_t x_347; size_t x_348; lean_object* x_349; lean_object* x_350; 
x_331 = lean_ctor_get(x_100, 1);
x_332 = lean_ctor_get(x_102, 1);
lean_inc(x_332);
lean_dec(x_102);
x_333 = lean_array_get_size(x_332);
x_334 = l_Lean_Expr_hash(x_1);
x_335 = lean_unsigned_to_nat(32u);
x_336 = lean_uint64_of_nat(x_335);
x_337 = lean_uint64_shift_right(x_334, x_336);
x_338 = lean_uint64_xor(x_334, x_337);
x_339 = lean_unsigned_to_nat(16u);
x_340 = lean_uint64_of_nat(x_339);
x_341 = lean_uint64_shift_right(x_338, x_340);
x_342 = lean_uint64_xor(x_338, x_341);
x_343 = lean_uint64_to_usize(x_342);
x_344 = lean_usize_of_nat(x_333);
lean_dec(x_333);
x_345 = lean_unsigned_to_nat(1u);
x_346 = lean_usize_of_nat(x_345);
x_347 = lean_usize_sub(x_344, x_346);
x_348 = lean_usize_land(x_343, x_347);
x_349 = lean_array_uget(x_332, x_348);
lean_dec(x_332);
x_350 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_1, x_349);
lean_dec(x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
lean_free_object(x_100);
x_351 = lean_mk_string_unchecked("binderNameHint", 14, 14);
x_352 = l_Lean_Name_mkStr1(x_351);
x_353 = lean_unsigned_to_nat(6u);
x_354 = l_Lean_Expr_isAppOfArity(x_1, x_352, x_353);
lean_dec(x_352);
if (x_354 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_1, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_1, 1);
lean_inc(x_356);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_355);
x_357 = l_Lean_Expr_resolveBinderNameHint_go(x_355, x_2, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_ctor_get(x_358, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
lean_dec(x_358);
lean_inc(x_2);
lean_inc(x_356);
x_362 = l_Lean_Expr_resolveBinderNameHint_go(x_356, x_2, x_361, x_4, x_5, x_359);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_371; size_t x_374; size_t x_375; uint8_t x_376; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = lean_ctor_get(x_363, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_367 = x_363;
} else {
 lean_dec_ref(x_363);
 x_367 = lean_box(0);
}
x_374 = lean_ptr_addr(x_355);
lean_dec(x_355);
x_375 = lean_ptr_addr(x_360);
x_376 = lean_usize_dec_eq(x_374, x_375);
if (x_376 == 0)
{
lean_dec(x_356);
x_371 = x_376;
goto block_373;
}
else
{
size_t x_377; size_t x_378; uint8_t x_379; 
x_377 = lean_ptr_addr(x_356);
lean_dec(x_356);
x_378 = lean_ptr_addr(x_365);
x_379 = lean_usize_dec_eq(x_377, x_378);
x_371 = x_379;
goto block_373;
}
block_370:
{
lean_object* x_369; 
lean_inc(x_368);
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_366);
x_16 = x_369;
x_17 = x_368;
x_18 = x_364;
goto block_94;
}
block_373:
{
if (x_371 == 0)
{
lean_object* x_372; 
x_372 = l_Lean_Expr_app___override(x_360, x_365);
x_368 = x_372;
goto block_370;
}
else
{
lean_dec(x_365);
lean_dec(x_360);
lean_inc(x_1);
x_368 = x_1;
goto block_370;
}
}
}
else
{
lean_dec(x_360);
lean_dec(x_356);
lean_dec(x_355);
x_95 = x_362;
goto block_99;
}
}
else
{
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_357;
goto block_99;
}
}
case 6:
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; 
x_380 = lean_ctor_get(x_1, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_1, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_1, 2);
lean_inc(x_382);
x_383 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_384 = l_Lean_Expr_resolveBinderNameHint_go(x_381, x_2, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_ctor_get(x_385, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_dec(x_385);
x_389 = lean_array_push(x_388, x_380);
lean_inc(x_2);
x_390 = l_Lean_Expr_resolveBinderNameHint_go(x_382, x_2, x_389, x_4, x_5, x_386);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_ctor_get(x_391, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_dec(x_391);
x_395 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_394);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_398 = x_395;
} else {
 lean_dec_ref(x_395);
 x_398 = lean_box(0);
}
x_399 = l_Lean_Expr_lam___override(x_396, x_387, x_393, x_383);
lean_inc(x_399);
if (lean_is_scalar(x_398)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_398;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_397);
x_16 = x_400;
x_17 = x_399;
x_18 = x_392;
goto block_94;
}
else
{
lean_dec(x_387);
x_95 = x_390;
goto block_99;
}
}
else
{
lean_dec(x_382);
lean_dec(x_380);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_384;
goto block_99;
}
}
case 7:
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_1, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_1, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_1, 2);
lean_inc(x_403);
x_404 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_405 = l_Lean_Expr_resolveBinderNameHint_go(x_402, x_2, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_array_push(x_409, x_401);
lean_inc(x_2);
x_411 = l_Lean_Expr_resolveBinderNameHint_go(x_403, x_2, x_410, x_4, x_5, x_407);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
lean_dec(x_412);
x_416 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_415);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
x_420 = l_Lean_Expr_forallE___override(x_417, x_408, x_414, x_404);
lean_inc(x_420);
if (lean_is_scalar(x_419)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_419;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_418);
x_16 = x_421;
x_17 = x_420;
x_18 = x_413;
goto block_94;
}
else
{
lean_dec(x_408);
x_95 = x_411;
goto block_99;
}
}
else
{
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_405;
goto block_99;
}
}
case 8:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; 
x_422 = lean_ctor_get(x_1, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_1, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_1, 2);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 3);
lean_inc(x_425);
x_426 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_427 = l_Lean_Expr_resolveBinderNameHint_go(x_423, x_2, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_432 = l_Lean_Expr_resolveBinderNameHint_go(x_424, x_2, x_431, x_4, x_5, x_429);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_433, 1);
lean_inc(x_436);
lean_dec(x_433);
x_437 = lean_array_push(x_436, x_422);
lean_inc(x_2);
x_438 = l_Lean_Expr_resolveBinderNameHint_go(x_425, x_2, x_437, x_4, x_5, x_434);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = lean_ctor_get(x_439, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
lean_dec(x_439);
x_443 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_442);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_446 = x_443;
} else {
 lean_dec_ref(x_443);
 x_446 = lean_box(0);
}
x_447 = l_Lean_Expr_letE___override(x_444, x_430, x_435, x_441, x_426);
lean_inc(x_447);
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_447);
lean_ctor_set(x_448, 1, x_445);
x_16 = x_448;
x_17 = x_447;
x_18 = x_440;
goto block_94;
}
else
{
lean_dec(x_435);
lean_dec(x_430);
x_95 = x_438;
goto block_99;
}
}
else
{
lean_dec(x_430);
lean_dec(x_425);
lean_dec(x_422);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_432;
goto block_99;
}
}
else
{
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_422);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_427;
goto block_99;
}
}
case 10:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_1, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_1, 1);
lean_inc(x_450);
lean_inc(x_2);
lean_inc(x_450);
x_451 = l_Lean_Expr_resolveBinderNameHint_go(x_450, x_2, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; size_t x_460; size_t x_461; uint8_t x_462; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_456 = x_452;
} else {
 lean_dec_ref(x_452);
 x_456 = lean_box(0);
}
x_460 = lean_ptr_addr(x_450);
lean_dec(x_450);
x_461 = lean_ptr_addr(x_454);
x_462 = lean_usize_dec_eq(x_460, x_461);
if (x_462 == 0)
{
lean_object* x_463; 
x_463 = l_Lean_Expr_mdata___override(x_449, x_454);
x_457 = x_463;
goto block_459;
}
else
{
lean_dec(x_454);
lean_dec(x_449);
lean_inc(x_1);
x_457 = x_1;
goto block_459;
}
block_459:
{
lean_object* x_458; 
lean_inc(x_457);
if (lean_is_scalar(x_456)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_456;
}
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_455);
x_16 = x_458;
x_17 = x_457;
x_18 = x_453;
goto block_94;
}
}
else
{
lean_dec(x_450);
lean_dec(x_449);
x_95 = x_451;
goto block_99;
}
}
case 11:
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_1, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_1, 1);
lean_inc(x_465);
x_466 = lean_ctor_get(x_1, 2);
lean_inc(x_466);
lean_inc(x_2);
lean_inc(x_466);
x_467 = l_Lean_Expr_resolveBinderNameHint_go(x_466, x_2, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; size_t x_476; size_t x_477; uint8_t x_478; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_ctor_get(x_468, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_468, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_472 = x_468;
} else {
 lean_dec_ref(x_468);
 x_472 = lean_box(0);
}
x_476 = lean_ptr_addr(x_466);
lean_dec(x_466);
x_477 = lean_ptr_addr(x_470);
x_478 = lean_usize_dec_eq(x_476, x_477);
if (x_478 == 0)
{
lean_object* x_479; 
x_479 = l_Lean_Expr_proj___override(x_464, x_465, x_470);
x_473 = x_479;
goto block_475;
}
else
{
lean_dec(x_470);
lean_dec(x_465);
lean_dec(x_464);
lean_inc(x_1);
x_473 = x_1;
goto block_475;
}
block_475:
{
lean_object* x_474; 
lean_inc(x_473);
if (lean_is_scalar(x_472)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_472;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_471);
x_16 = x_474;
x_17 = x_473;
x_18 = x_469;
goto block_94;
}
}
else
{
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_464);
x_95 = x_467;
goto block_99;
}
}
default: 
{
lean_object* x_480; 
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_1);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_1);
lean_ctor_set(x_480, 1, x_3);
lean_inc(x_1);
x_16 = x_480;
x_17 = x_1;
x_18 = x_331;
goto block_94;
}
}
}
else
{
lean_object* x_481; lean_object* x_482; 
x_481 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_482 = l_Lean_Expr_resolveBinderNameHint_go(x_481, x_2, x_3, x_4, x_5, x_331);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_ctor_get(x_483, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_483, 1);
lean_inc(x_486);
lean_dec(x_483);
x_487 = l_Lean_Expr_appFn_x21(x_1);
x_488 = l_Lean_Expr_appFn_x21(x_487);
x_489 = lean_alloc_closure((void*)(l_Lean_Expr_resolveBinderNameHint_go___lam__0___boxed), 7, 1);
lean_closure_set(x_489, 0, x_485);
lean_inc(x_489);
x_490 = lean_alloc_closure((void*)(l_Lean_Expr_resolveBinderNameHint_go___lam__1___boxed), 8, 1);
lean_closure_set(x_490, 0, x_489);
x_491 = l_Lean_Expr_appArg_x21(x_488);
lean_dec(x_488);
x_492 = l_Lean_Expr_appArg_x21(x_487);
lean_dec(x_487);
switch (lean_obj_tag(x_491)) {
case 0:
{
lean_object* x_493; lean_object* x_494; 
lean_dec(x_490);
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
lean_dec(x_491);
x_494 = l_Lean_Expr_headBeta(x_492);
switch (lean_obj_tag(x_494)) {
case 0:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
lean_dec(x_494);
x_496 = l_Lean_Expr_bvar___override(x_495);
lean_inc(x_2);
x_497 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_496, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_496);
lean_dec(x_493);
x_95 = x_497;
goto block_99;
}
case 1:
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_494, 0);
lean_inc(x_498);
lean_dec(x_494);
x_499 = l_Lean_Expr_fvar___override(x_498);
lean_inc(x_2);
x_500 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_499, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_499);
lean_dec(x_493);
x_95 = x_500;
goto block_99;
}
case 2:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_494, 0);
lean_inc(x_501);
lean_dec(x_494);
x_502 = l_Lean_Expr_mvar___override(x_501);
lean_inc(x_2);
x_503 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_502, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_502);
lean_dec(x_493);
x_95 = x_503;
goto block_99;
}
case 3:
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_494, 0);
lean_inc(x_504);
lean_dec(x_494);
x_505 = l_Lean_Expr_sort___override(x_504);
lean_inc(x_2);
x_506 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_505, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_505);
lean_dec(x_493);
x_95 = x_506;
goto block_99;
}
case 4:
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_494, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_494, 1);
lean_inc(x_508);
lean_dec(x_494);
x_509 = l_Lean_Expr_const___override(x_507, x_508);
lean_inc(x_2);
x_510 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_509, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_509);
lean_dec(x_493);
x_95 = x_510;
goto block_99;
}
case 5:
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_511 = lean_ctor_get(x_494, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_494, 1);
lean_inc(x_512);
lean_dec(x_494);
x_513 = l_Lean_Expr_app___override(x_511, x_512);
lean_inc(x_2);
x_514 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_513, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_513);
lean_dec(x_493);
x_95 = x_514;
goto block_99;
}
case 8:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; lean_object* x_521; 
x_515 = lean_ctor_get(x_494, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_494, 1);
lean_inc(x_516);
x_517 = lean_ctor_get(x_494, 2);
lean_inc(x_517);
x_518 = lean_ctor_get(x_494, 3);
lean_inc(x_518);
x_519 = lean_ctor_get_uint8(x_494, sizeof(void*)*4 + 8);
lean_dec(x_494);
x_520 = l_Lean_Expr_letE___override(x_515, x_516, x_517, x_518, x_519);
lean_inc(x_2);
x_521 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_520, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_520);
lean_dec(x_493);
x_95 = x_521;
goto block_99;
}
case 9:
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_494, 0);
lean_inc(x_522);
lean_dec(x_494);
x_523 = l_Lean_Expr_lit___override(x_522);
lean_inc(x_2);
x_524 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_523, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_523);
lean_dec(x_493);
x_95 = x_524;
goto block_99;
}
case 10:
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_525 = lean_ctor_get(x_494, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_494, 1);
lean_inc(x_526);
lean_dec(x_494);
x_527 = l_Lean_Expr_mdata___override(x_525, x_526);
lean_inc(x_2);
x_528 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_527, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_527);
lean_dec(x_493);
x_95 = x_528;
goto block_99;
}
case 11:
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_529 = lean_ctor_get(x_494, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_494, 1);
lean_inc(x_530);
x_531 = lean_ctor_get(x_494, 2);
lean_inc(x_531);
lean_dec(x_494);
x_532 = l_Lean_Expr_proj___override(x_529, x_530, x_531);
lean_inc(x_2);
x_533 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_345, x_489, x_493, x_532, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_532);
lean_dec(x_493);
x_95 = x_533;
goto block_99;
}
default: 
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; 
x_534 = lean_ctor_get(x_494, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_494, 1);
lean_inc(x_535);
x_536 = lean_ctor_get(x_494, 2);
lean_inc(x_536);
x_537 = lean_ctor_get_uint8(x_494, sizeof(void*)*3 + 8);
lean_dec(x_494);
lean_inc(x_2);
x_538 = l_Lean_Expr_resolveBinderNameHint_go___lam__3(x_489, x_493, x_534, x_535, x_536, x_537, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_536);
lean_dec(x_535);
lean_dec(x_493);
x_95 = x_538;
goto block_99;
}
}
}
case 6:
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; 
lean_dec(x_489);
x_539 = lean_ctor_get(x_491, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_491, 1);
lean_inc(x_540);
x_541 = lean_ctor_get(x_491, 2);
lean_inc(x_541);
x_542 = lean_ctor_get_uint8(x_491, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_543 = l_Lean_Expr_resolveBinderNameHint_go___lam__2(x_492, x_490, x_491, x_539, x_540, x_541, x_542, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
x_95 = x_543;
goto block_99;
}
case 7:
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; lean_object* x_548; 
lean_dec(x_489);
x_544 = lean_ctor_get(x_491, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_491, 1);
lean_inc(x_545);
x_546 = lean_ctor_get(x_491, 2);
lean_inc(x_546);
x_547 = lean_ctor_get_uint8(x_491, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_548 = l_Lean_Expr_resolveBinderNameHint_go___lam__2(x_492, x_490, x_491, x_544, x_545, x_546, x_547, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
x_95 = x_548;
goto block_99;
}
default: 
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_490);
x_549 = l_Lean_Expr_headBeta(x_492);
lean_inc(x_2);
x_550 = l_Lean_Expr_resolveBinderNameHint_go___lam__1(x_489, x_491, x_549, x_2, x_486, x_4, x_5, x_484);
lean_dec(x_549);
lean_dec(x_491);
x_95 = x_550;
goto block_99;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_482;
goto block_99;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_551 = lean_ctor_get(x_350, 0);
lean_inc(x_551);
lean_dec(x_350);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_3);
lean_ctor_set(x_100, 0, x_552);
return x_100;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint64_t x_558; lean_object* x_559; uint64_t x_560; uint64_t x_561; uint64_t x_562; lean_object* x_563; uint64_t x_564; uint64_t x_565; uint64_t x_566; size_t x_567; size_t x_568; lean_object* x_569; size_t x_570; size_t x_571; size_t x_572; lean_object* x_573; lean_object* x_574; 
x_553 = lean_ctor_get(x_100, 0);
x_554 = lean_ctor_get(x_100, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_100);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 x_556 = x_553;
} else {
 lean_dec_ref(x_553);
 x_556 = lean_box(0);
}
x_557 = lean_array_get_size(x_555);
x_558 = l_Lean_Expr_hash(x_1);
x_559 = lean_unsigned_to_nat(32u);
x_560 = lean_uint64_of_nat(x_559);
x_561 = lean_uint64_shift_right(x_558, x_560);
x_562 = lean_uint64_xor(x_558, x_561);
x_563 = lean_unsigned_to_nat(16u);
x_564 = lean_uint64_of_nat(x_563);
x_565 = lean_uint64_shift_right(x_562, x_564);
x_566 = lean_uint64_xor(x_562, x_565);
x_567 = lean_uint64_to_usize(x_566);
x_568 = lean_usize_of_nat(x_557);
lean_dec(x_557);
x_569 = lean_unsigned_to_nat(1u);
x_570 = lean_usize_of_nat(x_569);
x_571 = lean_usize_sub(x_568, x_570);
x_572 = lean_usize_land(x_567, x_571);
x_573 = lean_array_uget(x_555, x_572);
lean_dec(x_555);
x_574 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__0(lean_box(0), x_1, x_573);
lean_dec(x_573);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
x_575 = lean_mk_string_unchecked("binderNameHint", 14, 14);
x_576 = l_Lean_Name_mkStr1(x_575);
x_577 = lean_unsigned_to_nat(6u);
x_578 = l_Lean_Expr_isAppOfArity(x_1, x_576, x_577);
lean_dec(x_576);
if (x_578 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_556);
x_579 = lean_ctor_get(x_1, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_1, 1);
lean_inc(x_580);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_579);
x_581 = l_Lean_Expr_resolveBinderNameHint_go(x_579, x_2, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec(x_581);
x_584 = lean_ctor_get(x_582, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_582, 1);
lean_inc(x_585);
lean_dec(x_582);
lean_inc(x_2);
lean_inc(x_580);
x_586 = l_Lean_Expr_resolveBinderNameHint_go(x_580, x_2, x_585, x_4, x_5, x_583);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_595; size_t x_598; size_t x_599; uint8_t x_600; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_ctor_get(x_587, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_587, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_591 = x_587;
} else {
 lean_dec_ref(x_587);
 x_591 = lean_box(0);
}
x_598 = lean_ptr_addr(x_579);
lean_dec(x_579);
x_599 = lean_ptr_addr(x_584);
x_600 = lean_usize_dec_eq(x_598, x_599);
if (x_600 == 0)
{
lean_dec(x_580);
x_595 = x_600;
goto block_597;
}
else
{
size_t x_601; size_t x_602; uint8_t x_603; 
x_601 = lean_ptr_addr(x_580);
lean_dec(x_580);
x_602 = lean_ptr_addr(x_589);
x_603 = lean_usize_dec_eq(x_601, x_602);
x_595 = x_603;
goto block_597;
}
block_594:
{
lean_object* x_593; 
lean_inc(x_592);
if (lean_is_scalar(x_591)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_591;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_590);
x_16 = x_593;
x_17 = x_592;
x_18 = x_588;
goto block_94;
}
block_597:
{
if (x_595 == 0)
{
lean_object* x_596; 
x_596 = l_Lean_Expr_app___override(x_584, x_589);
x_592 = x_596;
goto block_594;
}
else
{
lean_dec(x_589);
lean_dec(x_584);
lean_inc(x_1);
x_592 = x_1;
goto block_594;
}
}
}
else
{
lean_dec(x_584);
lean_dec(x_580);
lean_dec(x_579);
x_95 = x_586;
goto block_99;
}
}
else
{
lean_dec(x_580);
lean_dec(x_579);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_581;
goto block_99;
}
}
case 6:
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; lean_object* x_608; 
lean_dec(x_556);
x_604 = lean_ctor_get(x_1, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_1, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_1, 2);
lean_inc(x_606);
x_607 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_608 = l_Lean_Expr_resolveBinderNameHint_go(x_605, x_2, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_611 = lean_ctor_get(x_609, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_609, 1);
lean_inc(x_612);
lean_dec(x_609);
x_613 = lean_array_push(x_612, x_604);
lean_inc(x_2);
x_614 = l_Lean_Expr_resolveBinderNameHint_go(x_606, x_2, x_613, x_4, x_5, x_610);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_ctor_get(x_615, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_615, 1);
lean_inc(x_618);
lean_dec(x_615);
x_619 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_618);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_622 = x_619;
} else {
 lean_dec_ref(x_619);
 x_622 = lean_box(0);
}
x_623 = l_Lean_Expr_lam___override(x_620, x_611, x_617, x_607);
lean_inc(x_623);
if (lean_is_scalar(x_622)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_622;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_621);
x_16 = x_624;
x_17 = x_623;
x_18 = x_616;
goto block_94;
}
else
{
lean_dec(x_611);
x_95 = x_614;
goto block_99;
}
}
else
{
lean_dec(x_606);
lean_dec(x_604);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_608;
goto block_99;
}
}
case 7:
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; lean_object* x_629; 
lean_dec(x_556);
x_625 = lean_ctor_get(x_1, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_1, 1);
lean_inc(x_626);
x_627 = lean_ctor_get(x_1, 2);
lean_inc(x_627);
x_628 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_629 = l_Lean_Expr_resolveBinderNameHint_go(x_626, x_2, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = lean_ctor_get(x_630, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_630, 1);
lean_inc(x_633);
lean_dec(x_630);
x_634 = lean_array_push(x_633, x_625);
lean_inc(x_2);
x_635 = l_Lean_Expr_resolveBinderNameHint_go(x_627, x_2, x_634, x_4, x_5, x_631);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_ctor_get(x_636, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
lean_dec(x_636);
x_640 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_639);
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_643 = x_640;
} else {
 lean_dec_ref(x_640);
 x_643 = lean_box(0);
}
x_644 = l_Lean_Expr_forallE___override(x_641, x_632, x_638, x_628);
lean_inc(x_644);
if (lean_is_scalar(x_643)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_643;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_642);
x_16 = x_645;
x_17 = x_644;
x_18 = x_637;
goto block_94;
}
else
{
lean_dec(x_632);
x_95 = x_635;
goto block_99;
}
}
else
{
lean_dec(x_627);
lean_dec(x_625);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_629;
goto block_99;
}
}
case 8:
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; lean_object* x_651; 
lean_dec(x_556);
x_646 = lean_ctor_get(x_1, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_1, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_1, 2);
lean_inc(x_648);
x_649 = lean_ctor_get(x_1, 3);
lean_inc(x_649);
x_650 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_651 = l_Lean_Expr_resolveBinderNameHint_go(x_647, x_2, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = lean_ctor_get(x_652, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_652, 1);
lean_inc(x_655);
lean_dec(x_652);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_656 = l_Lean_Expr_resolveBinderNameHint_go(x_648, x_2, x_655, x_4, x_5, x_653);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = lean_ctor_get(x_657, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_657, 1);
lean_inc(x_660);
lean_dec(x_657);
x_661 = lean_array_push(x_660, x_646);
lean_inc(x_2);
x_662 = l_Lean_Expr_resolveBinderNameHint_go(x_649, x_2, x_661, x_4, x_5, x_658);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_665 = lean_ctor_get(x_663, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_663, 1);
lean_inc(x_666);
lean_dec(x_663);
x_667 = l___private_Lean_Meta_BinderNameHint_0__Lean_exitScope(x_666);
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_670 = x_667;
} else {
 lean_dec_ref(x_667);
 x_670 = lean_box(0);
}
x_671 = l_Lean_Expr_letE___override(x_668, x_654, x_659, x_665, x_650);
lean_inc(x_671);
if (lean_is_scalar(x_670)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_670;
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_669);
x_16 = x_672;
x_17 = x_671;
x_18 = x_664;
goto block_94;
}
else
{
lean_dec(x_659);
lean_dec(x_654);
x_95 = x_662;
goto block_99;
}
}
else
{
lean_dec(x_654);
lean_dec(x_649);
lean_dec(x_646);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_656;
goto block_99;
}
}
else
{
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_646);
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_651;
goto block_99;
}
}
case 10:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_556);
x_673 = lean_ctor_get(x_1, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_1, 1);
lean_inc(x_674);
lean_inc(x_2);
lean_inc(x_674);
x_675 = l_Lean_Expr_resolveBinderNameHint_go(x_674, x_2, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; size_t x_684; size_t x_685; uint8_t x_686; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_678 = lean_ctor_get(x_676, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_676, 1);
lean_inc(x_679);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_680 = x_676;
} else {
 lean_dec_ref(x_676);
 x_680 = lean_box(0);
}
x_684 = lean_ptr_addr(x_674);
lean_dec(x_674);
x_685 = lean_ptr_addr(x_678);
x_686 = lean_usize_dec_eq(x_684, x_685);
if (x_686 == 0)
{
lean_object* x_687; 
x_687 = l_Lean_Expr_mdata___override(x_673, x_678);
x_681 = x_687;
goto block_683;
}
else
{
lean_dec(x_678);
lean_dec(x_673);
lean_inc(x_1);
x_681 = x_1;
goto block_683;
}
block_683:
{
lean_object* x_682; 
lean_inc(x_681);
if (lean_is_scalar(x_680)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_680;
}
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_679);
x_16 = x_682;
x_17 = x_681;
x_18 = x_677;
goto block_94;
}
}
else
{
lean_dec(x_674);
lean_dec(x_673);
x_95 = x_675;
goto block_99;
}
}
case 11:
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_556);
x_688 = lean_ctor_get(x_1, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_1, 1);
lean_inc(x_689);
x_690 = lean_ctor_get(x_1, 2);
lean_inc(x_690);
lean_inc(x_2);
lean_inc(x_690);
x_691 = l_Lean_Expr_resolveBinderNameHint_go(x_690, x_2, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; size_t x_700; size_t x_701; uint8_t x_702; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = lean_ctor_get(x_692, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_692, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 lean_ctor_release(x_692, 1);
 x_696 = x_692;
} else {
 lean_dec_ref(x_692);
 x_696 = lean_box(0);
}
x_700 = lean_ptr_addr(x_690);
lean_dec(x_690);
x_701 = lean_ptr_addr(x_694);
x_702 = lean_usize_dec_eq(x_700, x_701);
if (x_702 == 0)
{
lean_object* x_703; 
x_703 = l_Lean_Expr_proj___override(x_688, x_689, x_694);
x_697 = x_703;
goto block_699;
}
else
{
lean_dec(x_694);
lean_dec(x_689);
lean_dec(x_688);
lean_inc(x_1);
x_697 = x_1;
goto block_699;
}
block_699:
{
lean_object* x_698; 
lean_inc(x_697);
if (lean_is_scalar(x_696)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_696;
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_695);
x_16 = x_698;
x_17 = x_697;
x_18 = x_693;
goto block_94;
}
}
else
{
lean_dec(x_690);
lean_dec(x_689);
lean_dec(x_688);
x_95 = x_691;
goto block_99;
}
}
default: 
{
lean_object* x_704; 
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_1);
if (lean_is_scalar(x_556)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_556;
}
lean_ctor_set(x_704, 0, x_1);
lean_ctor_set(x_704, 1, x_3);
lean_inc(x_1);
x_16 = x_704;
x_17 = x_1;
x_18 = x_554;
goto block_94;
}
}
}
else
{
lean_object* x_705; lean_object* x_706; 
lean_dec(x_556);
x_705 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_706 = l_Lean_Expr_resolveBinderNameHint_go(x_705, x_2, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec(x_706);
x_709 = lean_ctor_get(x_707, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_707, 1);
lean_inc(x_710);
lean_dec(x_707);
x_711 = l_Lean_Expr_appFn_x21(x_1);
x_712 = l_Lean_Expr_appFn_x21(x_711);
x_713 = lean_alloc_closure((void*)(l_Lean_Expr_resolveBinderNameHint_go___lam__0___boxed), 7, 1);
lean_closure_set(x_713, 0, x_709);
lean_inc(x_713);
x_714 = lean_alloc_closure((void*)(l_Lean_Expr_resolveBinderNameHint_go___lam__1___boxed), 8, 1);
lean_closure_set(x_714, 0, x_713);
x_715 = l_Lean_Expr_appArg_x21(x_712);
lean_dec(x_712);
x_716 = l_Lean_Expr_appArg_x21(x_711);
lean_dec(x_711);
switch (lean_obj_tag(x_715)) {
case 0:
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_714);
x_717 = lean_ctor_get(x_715, 0);
lean_inc(x_717);
lean_dec(x_715);
x_718 = l_Lean_Expr_headBeta(x_716);
switch (lean_obj_tag(x_718)) {
case 0:
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
lean_dec(x_718);
x_720 = l_Lean_Expr_bvar___override(x_719);
lean_inc(x_2);
x_721 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_720, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_720);
lean_dec(x_717);
x_95 = x_721;
goto block_99;
}
case 1:
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_718, 0);
lean_inc(x_722);
lean_dec(x_718);
x_723 = l_Lean_Expr_fvar___override(x_722);
lean_inc(x_2);
x_724 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_723, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_723);
lean_dec(x_717);
x_95 = x_724;
goto block_99;
}
case 2:
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_718, 0);
lean_inc(x_725);
lean_dec(x_718);
x_726 = l_Lean_Expr_mvar___override(x_725);
lean_inc(x_2);
x_727 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_726, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_726);
lean_dec(x_717);
x_95 = x_727;
goto block_99;
}
case 3:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_718, 0);
lean_inc(x_728);
lean_dec(x_718);
x_729 = l_Lean_Expr_sort___override(x_728);
lean_inc(x_2);
x_730 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_729, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_729);
lean_dec(x_717);
x_95 = x_730;
goto block_99;
}
case 4:
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_731 = lean_ctor_get(x_718, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_718, 1);
lean_inc(x_732);
lean_dec(x_718);
x_733 = l_Lean_Expr_const___override(x_731, x_732);
lean_inc(x_2);
x_734 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_733, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_733);
lean_dec(x_717);
x_95 = x_734;
goto block_99;
}
case 5:
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_735 = lean_ctor_get(x_718, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_718, 1);
lean_inc(x_736);
lean_dec(x_718);
x_737 = l_Lean_Expr_app___override(x_735, x_736);
lean_inc(x_2);
x_738 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_737, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_737);
lean_dec(x_717);
x_95 = x_738;
goto block_99;
}
case 8:
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; uint8_t x_743; lean_object* x_744; lean_object* x_745; 
x_739 = lean_ctor_get(x_718, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_718, 1);
lean_inc(x_740);
x_741 = lean_ctor_get(x_718, 2);
lean_inc(x_741);
x_742 = lean_ctor_get(x_718, 3);
lean_inc(x_742);
x_743 = lean_ctor_get_uint8(x_718, sizeof(void*)*4 + 8);
lean_dec(x_718);
x_744 = l_Lean_Expr_letE___override(x_739, x_740, x_741, x_742, x_743);
lean_inc(x_2);
x_745 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_744, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_744);
lean_dec(x_717);
x_95 = x_745;
goto block_99;
}
case 9:
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_718, 0);
lean_inc(x_746);
lean_dec(x_718);
x_747 = l_Lean_Expr_lit___override(x_746);
lean_inc(x_2);
x_748 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_747, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_747);
lean_dec(x_717);
x_95 = x_748;
goto block_99;
}
case 10:
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_749 = lean_ctor_get(x_718, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_718, 1);
lean_inc(x_750);
lean_dec(x_718);
x_751 = l_Lean_Expr_mdata___override(x_749, x_750);
lean_inc(x_2);
x_752 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_751, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_751);
lean_dec(x_717);
x_95 = x_752;
goto block_99;
}
case 11:
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_753 = lean_ctor_get(x_718, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_718, 1);
lean_inc(x_754);
x_755 = lean_ctor_get(x_718, 2);
lean_inc(x_755);
lean_dec(x_718);
x_756 = l_Lean_Expr_proj___override(x_753, x_754, x_755);
lean_inc(x_2);
x_757 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_569, x_713, x_717, x_756, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_756);
lean_dec(x_717);
x_95 = x_757;
goto block_99;
}
default: 
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; lean_object* x_762; 
x_758 = lean_ctor_get(x_718, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_718, 1);
lean_inc(x_759);
x_760 = lean_ctor_get(x_718, 2);
lean_inc(x_760);
x_761 = lean_ctor_get_uint8(x_718, sizeof(void*)*3 + 8);
lean_dec(x_718);
lean_inc(x_2);
x_762 = l_Lean_Expr_resolveBinderNameHint_go___lam__3(x_713, x_717, x_758, x_759, x_760, x_761, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_760);
lean_dec(x_759);
lean_dec(x_717);
x_95 = x_762;
goto block_99;
}
}
}
case 6:
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; lean_object* x_767; 
lean_dec(x_713);
x_763 = lean_ctor_get(x_715, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_715, 1);
lean_inc(x_764);
x_765 = lean_ctor_get(x_715, 2);
lean_inc(x_765);
x_766 = lean_ctor_get_uint8(x_715, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_767 = l_Lean_Expr_resolveBinderNameHint_go___lam__2(x_716, x_714, x_715, x_763, x_764, x_765, x_766, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_765);
lean_dec(x_764);
lean_dec(x_763);
x_95 = x_767;
goto block_99;
}
case 7:
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; lean_object* x_772; 
lean_dec(x_713);
x_768 = lean_ctor_get(x_715, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_715, 1);
lean_inc(x_769);
x_770 = lean_ctor_get(x_715, 2);
lean_inc(x_770);
x_771 = lean_ctor_get_uint8(x_715, sizeof(void*)*3 + 8);
lean_inc(x_2);
x_772 = l_Lean_Expr_resolveBinderNameHint_go___lam__2(x_716, x_714, x_715, x_768, x_769, x_770, x_771, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_770);
lean_dec(x_769);
lean_dec(x_768);
x_95 = x_772;
goto block_99;
}
default: 
{
lean_object* x_773; lean_object* x_774; 
lean_dec(x_714);
x_773 = l_Lean_Expr_headBeta(x_716);
lean_inc(x_2);
x_774 = l_Lean_Expr_resolveBinderNameHint_go___lam__1(x_713, x_715, x_773, x_2, x_710, x_4, x_5, x_708);
lean_dec(x_773);
lean_dec(x_715);
x_95 = x_774;
goto block_99;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_95 = x_706;
goto block_99;
}
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_775 = lean_ctor_get(x_574, 0);
lean_inc(x_775);
lean_dec(x_574);
if (lean_is_scalar(x_556)) {
 x_776 = lean_alloc_ctor(0, 2, 0);
} else {
 x_776 = x_556;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_3);
x_777 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_554);
return x_777;
}
}
block_15:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_set(x_2, x_9, x_8);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
block_94:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_st_ref_take(x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Expr_hash(x_1);
x_27 = lean_unsigned_to_nat(32u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_sub(x_36, x_38);
x_40 = lean_usize_land(x_35, x_39);
x_41 = lean_array_uget(x_24, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_nat_add(x_23, x_37);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_17);
lean_ctor_set(x_44, 2, x_41);
x_45 = lean_array_uset(x_24, x_40, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_shiftl(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_45);
lean_ctor_set(x_20, 1, x_52);
lean_ctor_set(x_20, 0, x_43);
x_7 = x_16;
x_8 = x_21;
x_9 = x_20;
goto block_15;
}
else
{
lean_ctor_set(x_20, 1, x_45);
lean_ctor_set(x_20, 0, x_43);
x_7 = x_16;
x_8 = x_21;
x_9 = x_20;
goto block_15;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_box(0);
x_54 = lean_array_uset(x_24, x_40, x_53);
x_55 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_17, x_41);
x_56 = lean_array_uset(x_54, x_40, x_55);
lean_ctor_set(x_20, 1, x_56);
x_7 = x_16;
x_8 = x_21;
x_9 = x_20;
goto block_15;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; lean_object* x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; uint8_t x_76; 
x_57 = lean_ctor_get(x_20, 0);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_20);
x_59 = lean_array_get_size(x_58);
x_60 = l_Lean_Expr_hash(x_1);
x_61 = lean_unsigned_to_nat(32u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_unsigned_to_nat(16u);
x_66 = lean_uint64_of_nat(x_65);
x_67 = lean_uint64_shift_right(x_64, x_66);
x_68 = lean_uint64_xor(x_64, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_usize_of_nat(x_71);
x_73 = lean_usize_sub(x_70, x_72);
x_74 = lean_usize_land(x_69, x_73);
x_75 = lean_array_uget(x_58, x_74);
x_76 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__1(lean_box(0), x_1, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_nat_add(x_57, x_71);
lean_dec(x_57);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_17);
lean_ctor_set(x_78, 2, x_75);
x_79 = lean_array_uset(x_58, x_74, x_78);
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_nat_shiftl(x_77, x_80);
x_82 = lean_unsigned_to_nat(3u);
x_83 = lean_nat_div(x_81, x_82);
lean_dec(x_81);
x_84 = lean_array_get_size(x_79);
x_85 = lean_nat_dec_le(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__2(lean_box(0), x_79);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_86);
x_7 = x_16;
x_8 = x_21;
x_9 = x_87;
goto block_15;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_77);
lean_ctor_set(x_88, 1, x_79);
x_7 = x_16;
x_8 = x_21;
x_9 = x_88;
goto block_15;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_box(0);
x_90 = lean_array_uset(x_58, x_74, x_89);
x_91 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_MetavarContext_0__Lean_MetavarContext_MkBinding_visit_spec__5(lean_box(0), x_1, x_17, x_75);
x_92 = lean_array_uset(x_90, x_74, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_57);
lean_ctor_set(x_93, 1, x_92);
x_7 = x_16;
x_8 = x_21;
x_9 = x_93;
goto block_15;
}
}
}
block_99:
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_16 = x_96;
x_17 = x_98;
x_18 = x_97;
goto block_94;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_resolveBinderNameHint_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_resolveBinderNameHint_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Expr_resolveBinderNameHint_go___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Expr_resolveBinderNameHint_go___lam__3(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint_go___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_resolveBinderNameHint_go___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_shiftl(x_5, x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_nextPowerOfTwo(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_st_mk_ref(x_14, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_mk_empty_array_with_capacity(x_6);
lean_inc(x_16);
x_19 = l_Lean_Expr_resolveBinderNameHint_go(x_1, x_16, x_18, x_2, x_3, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_16, x_21);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_BinderNameHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderNameHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
