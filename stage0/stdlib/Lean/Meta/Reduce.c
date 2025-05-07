// Lean compiler output
// Module: Lean.Meta.Reduce
// Imports: Lean.Meta.Basic Lean.Meta.FunInfo Lean.Util.MonadCache
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
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1(uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___redArg(uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__0(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__1(uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___String_toNat_x21_spec__0(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___redArg(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_6, 1);
x_36 = lean_nat_dec_lt(x_8, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_14);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_array_get_size(x_38);
x_40 = lean_nat_dec_lt(x_8, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_array_get_size(x_7);
x_42 = lean_nat_dec_lt(x_8, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
x_15 = x_7;
x_16 = x_14;
goto block_20;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_array_fget(x_7, x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_44 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_43, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = lean_array_fset(x_7, x_8, x_47);
x_49 = lean_array_fset(x_48, x_8, x_45);
x_15 = x_49;
x_16 = x_46;
goto block_20;
}
else
{
uint8_t x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
if (x_1 == 0)
{
goto block_34;
}
else
{
if (x_5 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_array_fget(x_38, x_8);
x_55 = l_Lean_Meta_ParamInfo_isExplicit(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
x_15 = x_7;
x_16 = x_14;
goto block_20;
}
else
{
goto block_34;
}
}
else
{
goto block_34;
}
}
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
x_7 = x_15;
x_8 = x_18;
x_14 = x_16;
goto _start;
}
block_34:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_get_size(x_7);
x_22 = lean_nat_dec_lt(x_8, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
x_15 = x_7;
x_16 = x_14;
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fget(x_7, x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_23, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_7, x_8, x_27);
x_29 = lean_array_fset(x_28, x_8, x_25);
x_15 = x_29;
x_16 = x_26;
goto block_20;
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg___lam__0), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_13, x_12, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg___lam__0), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_4);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(x_13, x_12, x_1, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("runtime", 7, 7);
x_4 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_14, x_17);
lean_dec(x_14);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_5, 8);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 9);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 10);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_29 = lean_ctor_get(x_5, 11);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_31 = lean_ctor_get(x_5, 12);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_18);
lean_ctor_set(x_32, 4, x_15);
lean_ctor_set(x_32, 5, x_22);
lean_ctor_set(x_32, 6, x_23);
lean_ctor_set(x_32, 7, x_24);
lean_ctor_set(x_32, 8, x_25);
lean_ctor_set(x_32, 9, x_26);
lean_ctor_set(x_32, 10, x_27);
lean_ctor_set(x_32, 11, x_29);
lean_ctor_set(x_32, 12, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*13 + 1, x_30);
x_33 = lean_apply_6(x_1, x_2, x_3, x_4, x_32, x_6, x_7);
x_8 = x_33;
goto block_13;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___redArg(x_34, x_7);
x_8 = x_35;
goto block_13;
}
block_13:
{
if (lean_obj_tag(x_8) == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__0(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_mkLambdaFVars(x_6, x_15, x_4, x_5, x_4, x_18, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_19;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Meta_reduce_visit(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_mkForallFVars(x_6, x_15, x_4, x_5, x_18, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_19;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_114; 
if (x_4 == 0)
{
x_114 = x_11;
goto block_131;
}
else
{
lean_object* x_132; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_132 = l_Lean_Meta_isType(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_114 = x_135;
goto block_131;
}
else
{
uint8_t x_136; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_132, 0);
lean_dec(x_137);
lean_ctor_set(x_132, 0, x_2);
return x_132;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_dec(x_132);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_2);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_132);
if (x_140 == 0)
{
return x_132;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_mkAppN(x_14, x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_nat_add(x_19, x_1);
lean_dec(x_1);
lean_dec(x_19);
x_21 = l_Lean_mkRawNatLit(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
block_41:
{
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_1);
x_12 = x_25;
x_13 = x_24;
x_14 = x_27;
goto block_17;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_array_get(x_29, x_24, x_26);
lean_dec(x_26);
x_31 = l_Lean_Expr_isRawNatLit(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_1);
x_12 = x_25;
x_13 = x_24;
x_14 = x_27;
goto block_17;
}
else
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_24);
x_32 = l_Lean_Expr_rawNatLit_x3f(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_34 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_35 = lean_unsigned_to_nat(21u);
x_36 = lean_unsigned_to_nat(14u);
x_37 = lean_mk_string_unchecked("value is none", 13, 13);
x_38 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_33, x_34, x_35, x_36, x_37);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_panic___at___String_toNat_x21_spec__0(x_38);
x_18 = x_25;
x_19 = x_39;
goto block_23;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_18 = x_25;
x_19 = x_40;
goto block_23;
}
}
}
}
block_113:
{
lean_object* x_45; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = lean_whnf(x_2, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
switch (lean_obj_tag(x_46)) {
case 5:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Expr_getAppFn(x_46);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_Meta_reduce_visit(x_3, x_4, x_5, x_48, x_6, x_7, x_8, x_9, x_10, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Expr_getAppNumArgs(x_46);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_52);
lean_inc(x_50);
x_53 = l_Lean_Meta_getFunInfoNArgs(x_50, x_52, x_7, x_8, x_9, x_10, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
x_57 = l_Lean_Expr_sort___override(x_56);
lean_inc(x_52);
x_58 = lean_mk_array(x_52, x_57);
x_59 = lean_nat_sub(x_52, x_1);
lean_dec(x_52);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_46, x_58, x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get_size(x_60);
lean_inc(x_1);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_1);
x_64 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___redArg(x_3, x_4, x_5, x_54, x_43, x_63, x_60, x_61, x_6, x_7, x_8, x_9, x_10, x_55);
lean_dec(x_63);
lean_dec(x_54);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_mk_string_unchecked("Nat", 3, 3);
x_68 = lean_mk_string_unchecked("succ", 4, 4);
x_69 = l_Lean_Name_mkStr2(x_67, x_68);
x_70 = l_Lean_Expr_isConstOf(x_50, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
x_24 = x_65;
x_25 = x_66;
x_26 = x_61;
x_27 = x_50;
x_28 = x_70;
goto block_41;
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_array_get_size(x_65);
x_72 = lean_nat_dec_eq(x_71, x_1);
lean_dec(x_71);
x_24 = x_65;
x_25 = x_66;
x_26 = x_61;
x_27 = x_50;
x_28 = x_72;
goto block_41;
}
}
else
{
uint8_t x_73; 
lean_dec(x_50);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_64);
if (x_73 == 0)
{
return x_64;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_64, 0);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_64);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_53);
if (x_77 == 0)
{
return x_53;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_53, 0);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_53);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_49;
}
}
case 6:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_81 = lean_ctor_get(x_45, 1);
lean_inc(x_81);
lean_dec(x_45);
x_82 = lean_box(x_3);
x_83 = lean_box(x_4);
x_84 = lean_box(x_5);
x_85 = lean_box(x_43);
x_86 = lean_box(x_42);
x_87 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lam__0___boxed), 13, 5);
lean_closure_set(x_87, 0, x_82);
lean_closure_set(x_87, 1, x_83);
lean_closure_set(x_87, 2, x_84);
lean_closure_set(x_87, 3, x_85);
lean_closure_set(x_87, 4, x_86);
x_88 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg(x_46, x_87, x_43, x_6, x_7, x_8, x_9, x_10, x_81);
return x_88;
}
case 7:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_45, 1);
lean_inc(x_89);
lean_dec(x_45);
x_90 = lean_box(x_3);
x_91 = lean_box(x_4);
x_92 = lean_box(x_5);
x_93 = lean_box(x_43);
x_94 = lean_box(x_42);
x_95 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lam__1___boxed), 13, 5);
lean_closure_set(x_95, 0, x_90);
lean_closure_set(x_95, 1, x_91);
lean_closure_set(x_95, 2, x_92);
lean_closure_set(x_95, 3, x_93);
lean_closure_set(x_95, 4, x_94);
x_96 = l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___redArg(x_46, x_95, x_43, x_6, x_7, x_8, x_9, x_10, x_89);
return x_96;
}
case 11:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_1);
x_97 = lean_ctor_get(x_45, 1);
lean_inc(x_97);
lean_dec(x_45);
x_98 = lean_ctor_get(x_46, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_46, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_46, 2);
lean_inc(x_100);
lean_dec(x_46);
x_101 = l_Lean_Meta_reduce_visit(x_3, x_4, x_5, x_100, x_6, x_7, x_8, x_9, x_10, x_97);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = l_Lean_Expr_proj___override(x_98, x_99, x_103);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = l_Lean_Expr_proj___override(x_98, x_99, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_dec(x_99);
lean_dec(x_98);
return x_101;
}
}
default: 
{
uint8_t x_109; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_45);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_45, 0);
lean_dec(x_110);
return x_45;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_45, 1);
lean_inc(x_111);
lean_dec(x_45);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_46);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_45;
}
}
block_131:
{
lean_object* x_115; 
x_115 = lean_box(1);
if (x_5 == 0)
{
uint8_t x_116; 
x_116 = lean_unbox(x_115);
x_42 = x_116;
x_43 = x_5;
x_44 = x_114;
goto block_113;
}
else
{
lean_object* x_117; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_117 = l_Lean_Meta_isProof(x_2, x_7, x_8, x_9, x_10, x_114);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_unbox(x_115);
x_122 = lean_unbox(x_118);
lean_dec(x_118);
x_42 = x_121;
x_43 = x_122;
x_44 = x_120;
goto block_113;
}
else
{
uint8_t x_123; 
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_117);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_117, 0);
lean_dec(x_124);
lean_ctor_set(x_117, 0, x_2);
return x_117;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
lean_dec(x_117);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_2);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_117);
if (x_127 == 0)
{
return x_117;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_117, 0);
x_129 = lean_ctor_get(x_117, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_117);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_Expr_hash(x_4);
x_18 = lean_unsigned_to_nat(32u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_unsigned_to_nat(16u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_sub(x_27, x_29);
x_31 = lean_usize_land(x_26, x_30);
x_32 = lean_array_uget(x_15, x_31);
lean_dec(x_15);
x_33 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(x_4, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_11);
x_34 = lean_box(x_1);
x_35 = lean_box(x_2);
x_36 = lean_box(x_3);
lean_inc(x_4);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lam__2___boxed), 11, 5);
lean_closure_set(x_37, 0, x_28);
lean_closure_set(x_37, 1, x_4);
lean_closure_set(x_37, 2, x_34);
lean_closure_set(x_37, 3, x_35);
lean_closure_set(x_37, 4, x_36);
lean_inc(x_5);
x_38 = l_Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4___redArg(x_37, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_51; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_take(x_5, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
x_54 = lean_array_get_size(x_53);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = lean_usize_sub(x_55, x_29);
x_57 = lean_usize_land(x_26, x_56);
x_58 = lean_array_uget(x_53, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0(lean_box(0), x_4, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_60 = lean_nat_add(x_52, x_28);
lean_dec(x_52);
lean_inc(x_39);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_39);
lean_ctor_set(x_61, 2, x_58);
x_62 = lean_array_uset(x_53, x_57, x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_nat_shiftl(x_60, x_63);
x_65 = lean_unsigned_to_nat(3u);
x_66 = lean_nat_div(x_64, x_65);
lean_dec(x_64);
x_67 = lean_array_get_size(x_62);
x_68 = lean_nat_dec_le(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1(lean_box(0), x_62);
lean_ctor_set(x_42, 1, x_69);
lean_ctor_set(x_42, 0, x_60);
x_44 = x_42;
goto block_50;
}
else
{
lean_ctor_set(x_42, 1, x_62);
lean_ctor_set(x_42, 0, x_60);
x_44 = x_42;
goto block_50;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = lean_array_uset(x_53, x_57, x_70);
lean_inc(x_39);
x_72 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_4, x_39, x_58);
x_73 = lean_array_uset(x_71, x_57, x_72);
lean_ctor_set(x_42, 1, x_73);
x_44 = x_42;
goto block_50;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_42, 0);
x_75 = lean_ctor_get(x_42, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_42);
x_76 = lean_array_get_size(x_75);
x_77 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_78 = lean_usize_sub(x_77, x_29);
x_79 = lean_usize_land(x_26, x_78);
x_80 = lean_array_uget(x_75, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0(lean_box(0), x_4, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_82 = lean_nat_add(x_74, x_28);
lean_dec(x_74);
lean_inc(x_39);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_4);
lean_ctor_set(x_83, 1, x_39);
lean_ctor_set(x_83, 2, x_80);
x_84 = lean_array_uset(x_75, x_79, x_83);
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
x_91 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1(lean_box(0), x_84);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_91);
x_44 = x_92;
goto block_50;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_84);
x_44 = x_93;
goto block_50;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_box(0);
x_95 = lean_array_uset(x_75, x_79, x_94);
lean_inc(x_39);
x_96 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_4, x_39, x_80);
x_97 = lean_array_uset(x_95, x_79, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_74);
lean_ctor_set(x_98, 1, x_97);
x_44 = x_98;
goto block_50;
}
}
block_50:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_st_ref_set(x_5, x_44, x_43);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_39);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
}
else
{
lean_object* x_99; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_99 = lean_ctor_get(x_33, 0);
lean_inc(x_99);
lean_dec(x_33);
lean_ctor_set(x_11, 0, x_99);
return x_11;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; lean_object* x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; size_t x_113; size_t x_114; lean_object* x_115; size_t x_116; size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; 
x_100 = lean_ctor_get(x_11, 0);
x_101 = lean_ctor_get(x_11, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_11);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_array_get_size(x_102);
x_104 = l_Lean_Expr_hash(x_4);
x_105 = lean_unsigned_to_nat(32u);
x_106 = lean_uint64_of_nat(x_105);
x_107 = lean_uint64_shift_right(x_104, x_106);
x_108 = lean_uint64_xor(x_104, x_107);
x_109 = lean_unsigned_to_nat(16u);
x_110 = lean_uint64_of_nat(x_109);
x_111 = lean_uint64_shift_right(x_108, x_110);
x_112 = lean_uint64_xor(x_108, x_111);
x_113 = lean_uint64_to_usize(x_112);
x_114 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_usize_of_nat(x_115);
x_117 = lean_usize_sub(x_114, x_116);
x_118 = lean_usize_land(x_113, x_117);
x_119 = lean_array_uget(x_102, x_118);
lean_dec(x_102);
x_120 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(x_4, x_119);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_box(x_1);
x_122 = lean_box(x_2);
x_123 = lean_box(x_3);
lean_inc(x_4);
x_124 = lean_alloc_closure((void*)(l_Lean_Meta_reduce_visit___lam__2___boxed), 11, 5);
lean_closure_set(x_124, 0, x_115);
lean_closure_set(x_124, 1, x_4);
lean_closure_set(x_124, 2, x_121);
lean_closure_set(x_124, 3, x_122);
lean_closure_set(x_124, 4, x_123);
lean_inc(x_5);
x_125 = l_Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4___redArg(x_124, x_5, x_6, x_7, x_8, x_9, x_101);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; size_t x_141; size_t x_142; size_t x_143; lean_object* x_144; uint8_t x_145; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_st_ref_take(x_5, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_129, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_139 = x_129;
} else {
 lean_dec_ref(x_129);
 x_139 = lean_box(0);
}
x_140 = lean_array_get_size(x_138);
x_141 = lean_usize_of_nat(x_140);
lean_dec(x_140);
x_142 = lean_usize_sub(x_141, x_116);
x_143 = lean_usize_land(x_113, x_142);
x_144 = lean_array_uget(x_138, x_143);
x_145 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0(lean_box(0), x_4, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_nat_add(x_137, x_115);
lean_dec(x_137);
lean_inc(x_126);
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_126);
lean_ctor_set(x_147, 2, x_144);
x_148 = lean_array_uset(x_138, x_143, x_147);
x_149 = lean_unsigned_to_nat(2u);
x_150 = lean_nat_shiftl(x_146, x_149);
x_151 = lean_unsigned_to_nat(3u);
x_152 = lean_nat_div(x_150, x_151);
lean_dec(x_150);
x_153 = lean_array_get_size(x_148);
x_154 = lean_nat_dec_le(x_152, x_153);
lean_dec(x_153);
lean_dec(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1(lean_box(0), x_148);
if (lean_is_scalar(x_139)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_139;
}
lean_ctor_set(x_156, 0, x_146);
lean_ctor_set(x_156, 1, x_155);
x_131 = x_156;
goto block_136;
}
else
{
lean_object* x_157; 
if (lean_is_scalar(x_139)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_139;
}
lean_ctor_set(x_157, 0, x_146);
lean_ctor_set(x_157, 1, x_148);
x_131 = x_157;
goto block_136;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_box(0);
x_159 = lean_array_uset(x_138, x_143, x_158);
lean_inc(x_126);
x_160 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_reduce_visit_spec__6___redArg(x_4, x_126, x_144);
x_161 = lean_array_uset(x_159, x_143, x_160);
if (lean_is_scalar(x_139)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_139;
}
lean_ctor_set(x_162, 0, x_137);
lean_ctor_set(x_162, 1, x_161);
x_131 = x_162;
goto block_136;
}
block_136:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_st_ref_set(x_5, x_131, x_130);
lean_dec(x_5);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_125;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_163 = lean_ctor_get(x_120, 0);
lean_inc(x_163);
lean_dec(x_120);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_101);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_reduce_visit_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___redArg(x_15, x_16, x_17, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_reduce_visit_spec__1(x_17, x_18, x_19, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
lean_dec(x_4);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_lambdaTelescope___at___Lean_Meta_reduce_visit_spec__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_forallTelescope___at___Lean_Meta_reduce_visit_spec__3(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___Lean_Core_withIncRecDepth___at___Lean_Meta_reduce_visit_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lean_Meta_reduce_visit___lam__0(x_14, x_15, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = l_Lean_Meta_reduce_visit___lam__1(x_14, x_15, x_16, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_reduce_visit___lam__2(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_reduce_visit(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_10, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_st_mk_ref(x_19, x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = l_Lean_Meta_reduce_visit(x_2, x_3, x_4, x_1, x_21, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_21, x_25);
lean_dec(x_21);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_dec(x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_reduce(x_1, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = lean_unbox(x_7);
x_10 = lean_unbox(x_7);
x_11 = l_Lean_Meta_reduce(x_1, x_8, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
