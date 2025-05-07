// Lean compiler output
// Module: Lean.Compiler.LCNF.MonoTypes
// Imports: Lean.Meta.InferType Lean.Compiler.LCNF.Util Lean.Compiler.LCNF.BaseTypes Lean.Compiler.LCNF.CompilerM
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoTypeExt;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__2(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instReprTrivialStructureInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes_go(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toMonoType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclBaseType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isRuntimeBultinType(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1659_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249_(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_19; lean_object* x_20; 
x_19 = lean_usize_dec_lt(x_3, x_2);
if (x_19 == 0)
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_array_uget(x_33, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = lean_infer_type(x_34, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_38 = l_Lean_Meta_isProp(x_36, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = l_Lean_Meta_isTypeFormerType(x_36, x_5, x_6, x_7, x_8, x_41);
x_20 = x_42;
goto block_31;
}
else
{
lean_dec(x_36);
x_20 = x_38;
goto block_31;
}
}
else
{
lean_dec(x_36);
x_20 = x_38;
goto block_31;
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_box(x_11);
x_13 = lean_array_push(x_4, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_13;
x_9 = x_10;
goto _start;
}
block_31:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_10 = x_23;
x_11 = x_19;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
x_10 = x_24;
x_11 = x_26;
goto block_18;
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_2);
x_13 = l_Array_toSubarray___redArg(x_2, x_11, x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(x_13, x_15, x_17, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_box(0);
x_11 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_to_nat(x_14);
x_16 = lean_nat_pow(x_12, x_15);
lean_dec(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = lean_usize_to_nat(x_17);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_dec(x_18);
lean_inc(x_19);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_19);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_11);
lean_inc(x_11);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_11);
lean_inc(x_11);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_11);
lean_inc(x_11);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_11);
lean_inc(x_11);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_11);
lean_inc(x_11);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_11);
lean_inc(x_21);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
lean_ctor_set(x_27, 8, x_26);
lean_inc(x_11);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_11);
lean_inc(x_11);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_11);
lean_inc(x_11);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_11);
lean_inc(x_11);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_11);
lean_inc(x_31);
lean_inc(x_28);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_31);
lean_inc(x_19);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_19);
lean_inc(x_19);
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set(x_34, 3, x_20);
lean_ctor_set_usize(x_34, 4, x_14);
lean_inc(x_11);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_11);
lean_inc_n(x_21, 2);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_10);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_st_mk_ref(x_37, x_7);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(1);
x_42 = lean_box(1);
x_43 = lean_box(0);
x_44 = lean_box(2);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_11);
x_46 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set(x_46, 1, x_19);
lean_ctor_set(x_46, 2, x_20);
lean_ctor_set(x_46, 3, x_20);
lean_ctor_set_usize(x_46, 4, x_14);
lean_inc(x_9);
x_47 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed), 8, 1);
lean_closure_set(x_47, 0, x_9);
x_48 = lean_ctor_get(x_9, 0);
lean_inc(x_48);
lean_dec(x_9);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 0, 18);
x_51 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 0, x_51);
x_52 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 1, x_52);
x_53 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 2, x_53);
x_54 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 3, x_54);
x_55 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 4, x_55);
x_56 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 5, x_56);
x_57 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 6, x_57);
x_58 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, 7, x_58);
x_59 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 8, x_59);
x_60 = lean_unbox(x_42);
lean_ctor_set_uint8(x_50, 9, x_60);
x_61 = lean_unbox(x_43);
lean_ctor_set_uint8(x_50, 10, x_61);
x_62 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 11, x_62);
x_63 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 12, x_63);
x_64 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 13, x_64);
x_65 = lean_unbox(x_44);
lean_ctor_set_uint8(x_50, 14, x_65);
x_66 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 15, x_66);
x_67 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 16, x_67);
x_68 = lean_unbox(x_41);
lean_ctor_set_uint8(x_50, 17, x_68);
x_69 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_50);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_45);
lean_ctor_set(x_70, 1, x_46);
lean_ctor_set(x_70, 2, x_10);
x_71 = lean_mk_empty_array_with_capacity(x_20);
x_72 = lean_box(0);
x_73 = lean_box(0);
x_74 = lean_ctor_get(x_48, 2);
lean_inc(x_74);
lean_dec(x_48);
x_75 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_10);
lean_ctor_set(x_75, 2, x_70);
lean_ctor_set(x_75, 3, x_71);
lean_ctor_set(x_75, 4, x_72);
lean_ctor_set(x_75, 5, x_20);
lean_ctor_set(x_75, 6, x_73);
lean_ctor_set_uint64(x_75, sizeof(void*)*7, x_69);
x_76 = lean_unbox(x_49);
lean_ctor_set_uint8(x_75, sizeof(void*)*7 + 8, x_76);
x_77 = lean_unbox(x_49);
lean_ctor_set_uint8(x_75, sizeof(void*)*7 + 9, x_77);
x_78 = lean_unbox(x_49);
lean_ctor_set_uint8(x_75, sizeof(void*)*7 + 10, x_78);
x_79 = lean_unbox(x_49);
lean_inc(x_39);
x_80 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_74, x_47, x_79, x_75, x_39, x_2, x_3, x_40);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_39, x_82);
lean_dec(x_39);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_dec(x_39);
return x_80;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; lean_object* x_95; size_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint64_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; 
x_88 = lean_ctor_get(x_6, 0);
lean_inc(x_88);
lean_dec(x_6);
x_89 = lean_box(0);
x_90 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_unsigned_to_nat(5u);
x_93 = lean_usize_of_nat(x_92);
x_94 = lean_usize_to_nat(x_93);
x_95 = lean_nat_pow(x_91, x_94);
lean_dec(x_94);
x_96 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_97 = lean_usize_to_nat(x_96);
x_98 = lean_mk_empty_array_with_capacity(x_97);
lean_dec(x_97);
lean_inc(x_98);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_unsigned_to_nat(0u);
lean_inc(x_90);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_90);
lean_inc(x_90);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_90);
lean_inc(x_90);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_90);
lean_inc(x_90);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_90);
lean_inc(x_90);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_90);
lean_inc(x_90);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_90);
lean_inc(x_101);
x_107 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_100);
lean_ctor_set(x_107, 3, x_101);
lean_ctor_set(x_107, 4, x_102);
lean_ctor_set(x_107, 5, x_103);
lean_ctor_set(x_107, 6, x_104);
lean_ctor_set(x_107, 7, x_105);
lean_ctor_set(x_107, 8, x_106);
lean_inc(x_90);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_90);
lean_inc(x_90);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_90);
lean_inc(x_90);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_90);
lean_inc(x_90);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_90);
lean_inc(x_111);
lean_inc(x_108);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_108);
lean_ctor_set(x_112, 4, x_111);
lean_ctor_set(x_112, 5, x_111);
lean_inc(x_98);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_98);
lean_inc(x_98);
x_114 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_98);
lean_ctor_set(x_114, 2, x_100);
lean_ctor_set(x_114, 3, x_100);
lean_ctor_set_usize(x_114, 4, x_93);
lean_inc(x_90);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_90);
lean_inc_n(x_101, 2);
x_116 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_116, 0, x_101);
lean_ctor_set(x_116, 1, x_101);
lean_ctor_set(x_116, 2, x_101);
lean_ctor_set(x_116, 3, x_115);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_112);
lean_ctor_set(x_117, 2, x_89);
lean_ctor_set(x_117, 3, x_114);
lean_ctor_set(x_117, 4, x_116);
x_118 = lean_st_mk_ref(x_117, x_7);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_box(1);
x_122 = lean_box(1);
x_123 = lean_box(0);
x_124 = lean_box(2);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_90);
x_126 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_126, 0, x_99);
lean_ctor_set(x_126, 1, x_98);
lean_ctor_set(x_126, 2, x_100);
lean_ctor_set(x_126, 3, x_100);
lean_ctor_set_usize(x_126, 4, x_93);
lean_inc(x_88);
x_127 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed), 8, 1);
lean_closure_set(x_127, 0, x_88);
x_128 = lean_ctor_get(x_88, 0);
lean_inc(x_128);
lean_dec(x_88);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 0, 18);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, 0, x_131);
x_132 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, 1, x_132);
x_133 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, 2, x_133);
x_134 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, 3, x_134);
x_135 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, 4, x_135);
x_136 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 5, x_136);
x_137 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 6, x_137);
x_138 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, 7, x_138);
x_139 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 8, x_139);
x_140 = lean_unbox(x_122);
lean_ctor_set_uint8(x_130, 9, x_140);
x_141 = lean_unbox(x_123);
lean_ctor_set_uint8(x_130, 10, x_141);
x_142 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 11, x_142);
x_143 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 12, x_143);
x_144 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 13, x_144);
x_145 = lean_unbox(x_124);
lean_ctor_set_uint8(x_130, 14, x_145);
x_146 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 15, x_146);
x_147 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 16, x_147);
x_148 = lean_unbox(x_121);
lean_ctor_set_uint8(x_130, 17, x_148);
x_149 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_130);
x_150 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_150, 0, x_125);
lean_ctor_set(x_150, 1, x_126);
lean_ctor_set(x_150, 2, x_89);
x_151 = lean_mk_empty_array_with_capacity(x_100);
x_152 = lean_box(0);
x_153 = lean_box(0);
x_154 = lean_ctor_get(x_128, 2);
lean_inc(x_154);
lean_dec(x_128);
x_155 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_155, 0, x_130);
lean_ctor_set(x_155, 1, x_89);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set(x_155, 4, x_152);
lean_ctor_set(x_155, 5, x_100);
lean_ctor_set(x_155, 6, x_153);
lean_ctor_set_uint64(x_155, sizeof(void*)*7, x_149);
x_156 = lean_unbox(x_129);
lean_ctor_set_uint8(x_155, sizeof(void*)*7 + 8, x_156);
x_157 = lean_unbox(x_129);
lean_ctor_set_uint8(x_155, sizeof(void*)*7 + 9, x_157);
x_158 = lean_unbox(x_129);
lean_ctor_set_uint8(x_155, sizeof(void*)*7 + 10, x_158);
x_159 = lean_unbox(x_129);
lean_inc(x_119);
x_160 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_154, x_127, x_159, x_155, x_119, x_2, x_3, x_120);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_st_ref_get(x_119, x_162);
lean_dec(x_119);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_dec(x_119);
return x_160;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_6);
x_167 = lean_ctor_get(x_5, 1);
lean_inc(x_167);
lean_dec(x_5);
x_168 = lean_mk_string_unchecked("Lean.Compiler.LCNF.MonoTypes", 28, 28);
x_169 = lean_mk_string_unchecked("Lean.Compiler.LCNF.getRelevantCtorFields", 40, 40);
x_170 = lean_unsigned_to_nat(19u);
x_171 = lean_unsigned_to_nat(47u);
x_172 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_173 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_168, x_169, x_170, x_171, x_172);
lean_dec(x_172);
lean_dec(x_169);
lean_dec(x_168);
x_174 = l_panic___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__1(x_173, x_2, x_3, x_167);
return x_174;
}
}
else
{
uint8_t x_175; 
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_5);
if (x_175 == 0)
{
return x_5;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_5, 0);
x_177 = lean_ctor_get(x_5, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_5);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_getRelevantCtorFields_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getRelevantCtorFields___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("ctorName", 8, 8);
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
x_10 = lean_unsigned_to_nat(12u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Name_reprPrec(x_12, x_13);
lean_inc(x_11);
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
x_25 = lean_mk_string_unchecked("numParams", 9, 9);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(13u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unbox(x_16);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_21);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
x_40 = lean_mk_string_unchecked("fieldIdx", 8, 8);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unbox(x_16);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_mk_string_unchecked(" }", 2, 2);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_to_int(x_52);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_2);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_unbox(x_16);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
return x_59;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo___redArg____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_MonoTypes_0__Lean_Compiler_LCNF_reprTrivialStructureInfo____x40_Lean_Compiler_LCNF_MonoTypes___hyg_249____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_nat_dec_lt(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_box(0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_array_fget(x_3, x_6);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_23);
x_8 = x_26;
x_9 = x_7;
goto block_13;
}
else
{
if (lean_obj_tag(x_23) == 0)
{
goto block_22;
}
else
{
if (x_25 == 0)
{
lean_dec(x_23);
goto block_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_18);
lean_inc(x_2);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_6);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_8 = x_21;
x_9 = x_7;
goto block_13;
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_5 = x_8;
x_6 = x_11;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; 
x_9 = l_Lean_Compiler_LCNF_isRuntimeBultinType(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_78; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_78 = lean_ctor_get_uint8(x_14, sizeof(void*)*6 + 1);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
x_15 = x_79;
goto block_77;
}
else
{
x_15 = x_78;
goto block_77;
}
block_77:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_5 = x_12;
goto block_8;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_dec(x_20);
lean_inc(x_19);
x_21 = l_Lean_Compiler_LCNF_getRelevantCtorFields(x_19, x_2, x_3, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_size(x_22);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_box(0);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 1, x_24);
lean_ctor_set(x_16, 0, x_29);
x_30 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg(x_14, x_19, x_22, x_28, x_16, x_25, x_23);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_14);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_31);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_41);
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_14);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_21, 0);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_21);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
lean_dec(x_16);
lean_inc(x_49);
x_50 = l_Lean_Compiler_LCNF_getRelevantCtorFields(x_49, x_2, x_3, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_51);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
x_60 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg(x_14, x_49, x_51, x_57, x_59, x_54, x_52);
lean_dec(x_57);
lean_dec(x_51);
lean_dec(x_14);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
lean_dec(x_62);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_49);
lean_dec(x_14);
x_71 = lean_ctor_get(x_50, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_73 = x_50;
} else {
 lean_dec_ref(x_50);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_5 = x_12;
goto block_8;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_13;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_12);
return x_76;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_10, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set(x_10, 0, x_82);
return x_10;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_10, 1);
lean_inc(x_83);
lean_dec(x_10);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_10);
if (x_86 == 0)
{
return x_10;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_10, 0);
x_88 = lean_ctor_get(x_10, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_10);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_4);
return x_91;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_hasTrivialStructure_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_push(x_2, x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getParamTypes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Lean_Compiler_LCNF_getParamTypes_go(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(1);
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_isErased(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_5);
return x_8;
}
else
{
if (x_4 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_5);
return x_13;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("Lean.Compiler.LCNF.MonoTypes", 28, 28);
x_8 = lean_mk_string_unchecked("Lean.Compiler.LCNF.toMonoType.visitApp", 38, 38);
x_9 = lean_unsigned_to_nat(104u);
x_10 = lean_unsigned_to_nat(50u);
x_11 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_12 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_13 = l_panic___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__1(x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_15; uint8_t x_30; 
x_30 = lean_usize_dec_lt(x_3, x_2);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec(x_5);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_dec(x_4);
lean_inc(x_33);
x_34 = l_Lean_Expr_headBeta(x_33);
switch (lean_obj_tag(x_34)) {
case 0:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Expr_bvar___override(x_35);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_36, x_5, x_6, x_7);
lean_dec(x_36);
x_15 = x_37;
goto block_29;
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Lean_Expr_fvar___override(x_38);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_39, x_5, x_6, x_7);
lean_dec(x_39);
x_15 = x_40;
goto block_29;
}
case 2:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
x_42 = l_Lean_Expr_mvar___override(x_41);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_42, x_5, x_6, x_7);
lean_dec(x_42);
x_15 = x_43;
goto block_29;
}
case 3:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l_Lean_Expr_sort___override(x_44);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_45, x_5, x_6, x_7);
lean_dec(x_45);
x_15 = x_46;
goto block_29;
}
case 4:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_dec(x_34);
x_49 = l_Lean_Expr_const___override(x_47, x_48);
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_49, x_5, x_6, x_7);
lean_dec(x_49);
x_15 = x_50;
goto block_29;
}
case 5:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_34, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_dec(x_34);
x_53 = l_Lean_Expr_app___override(x_51, x_52);
lean_inc(x_6);
lean_inc(x_5);
x_54 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_53, x_5, x_6, x_7);
lean_dec(x_53);
x_15 = x_54;
goto block_29;
}
case 6:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_34, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_34, 2);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_34, sizeof(void*)*3 + 8);
lean_dec(x_34);
x_59 = l_Lean_Expr_lam___override(x_55, x_56, x_57, x_58);
lean_inc(x_6);
lean_inc(x_5);
x_60 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_59, x_5, x_6, x_7);
lean_dec(x_59);
x_15 = x_60;
goto block_29;
}
case 7:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_73; 
lean_dec(x_33);
x_61 = lean_ctor_get(x_34, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_34, 2);
lean_inc(x_62);
lean_dec(x_34);
x_63 = lean_array_uget(x_1, x_3);
x_64 = l_Lean_Expr_headBeta(x_63);
switch (lean_obj_tag(x_61)) {
case 3:
{
lean_dec(x_61);
x_73 = x_30;
goto block_82;
}
case 4:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_61, 0);
lean_inc(x_83);
lean_dec(x_61);
if (lean_obj_tag(x_83) == 1)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_mk_string_unchecked("lcErased", 8, 8);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_87; 
x_87 = lean_string_dec_eq(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
x_73 = x_87;
goto block_82;
}
else
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
goto block_72;
}
}
else
{
lean_dec(x_83);
goto block_72;
}
}
default: 
{
lean_dec(x_61);
goto block_72;
}
}
block_69:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_expr_instantiate1(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_8 = x_68;
x_9 = x_66;
goto block_14;
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lean_Compiler_LCNF_anyExpr;
x_71 = l_Lean_Expr_app___override(x_32, x_70);
x_65 = x_71;
x_66 = x_7;
goto block_69;
}
block_82:
{
if (x_73 == 0)
{
goto block_72;
}
else
{
lean_object* x_74; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
x_74 = l_Lean_Compiler_LCNF_toMonoType(x_64, x_5, x_6, x_7);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Expr_app___override(x_32, x_75);
x_65 = x_77;
x_66 = x_76;
goto block_69;
}
else
{
uint8_t x_78; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 0);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_74);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
case 8:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_34, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_34, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_34, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_34, 3);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_34, sizeof(void*)*4 + 8);
lean_dec(x_34);
x_93 = l_Lean_Expr_letE___override(x_88, x_89, x_90, x_91, x_92);
lean_inc(x_6);
lean_inc(x_5);
x_94 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_93, x_5, x_6, x_7);
lean_dec(x_93);
x_15 = x_94;
goto block_29;
}
case 9:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_34, 0);
lean_inc(x_95);
lean_dec(x_34);
x_96 = l_Lean_Expr_lit___override(x_95);
lean_inc(x_6);
lean_inc(x_5);
x_97 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_96, x_5, x_6, x_7);
lean_dec(x_96);
x_15 = x_97;
goto block_29;
}
case 10:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_34, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_34, 1);
lean_inc(x_99);
lean_dec(x_34);
x_100 = l_Lean_Expr_mdata___override(x_98, x_99);
lean_inc(x_6);
lean_inc(x_5);
x_101 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_100, x_5, x_6, x_7);
lean_dec(x_100);
x_15 = x_101;
goto block_29;
}
default: 
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_34, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_34, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_34, 2);
lean_inc(x_104);
lean_dec(x_34);
x_105 = l_Lean_Expr_proj___override(x_102, x_103, x_104);
lean_inc(x_6);
lean_inc(x_5);
x_106 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_32, x_33, x_105, x_5, x_6, x_7);
lean_dec(x_105);
x_15 = x_106;
goto block_29;
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_8;
x_7 = x_9;
goto _start;
}
block_29:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_15, 0, x_19);
return x_15;
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_8 = x_24;
x_9 = x_23;
goto block_14;
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_8 = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_11 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_const___override(x_3, x_15);
lean_ctor_set(x_11, 1, x_13);
lean_ctor_set(x_11, 0, x_16);
x_17 = lean_array_size(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2(x_1, x_17, x_19, x_11, x_5, x_6, x_14);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
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
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; size_t x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_box(0);
x_35 = l_Lean_Expr_const___override(x_3, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_array_size(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_usize_of_nat(x_38);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2(x_1, x_37, x_39, x_36, x_5, x_6, x_33);
lean_dec(x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_48 = x_40;
} else {
 lean_dec_ref(x_40);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_dec(x_8);
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
x_54 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_52, x_53, x_5, x_6, x_50);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
x_59 = l_Array_toSubarray___redArg(x_1, x_57, x_58);
x_60 = l_Array_ofSubarray___redArg(x_59);
lean_dec(x_59);
x_61 = l_Lean_Compiler_LCNF_instantiateForall(x_55, x_60, x_5, x_6, x_56);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Compiler_LCNF_getParamTypes(x_62);
x_65 = lean_ctor_get(x_51, 2);
lean_inc(x_65);
lean_dec(x_51);
x_66 = lean_array_get(x_2, x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
x_67 = l_Lean_Compiler_LCNF_toMonoType(x_66, x_5, x_6, x_63);
return x_67;
}
else
{
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_61;
}
}
else
{
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_54;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_8);
if (x_68 == 0)
{
return x_8;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_8, 0);
x_70 = lean_ctor_get(x_8, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_8);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_mk_string_unchecked("Bool", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_anyExpr;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
goto block_7;
}
else
{
if (x_10 == 0)
{
lean_dec(x_9);
goto block_7;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_usize_of_nat(x_8);
x_12 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_13 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(x_1, x_11, x_12);
if (x_13 == 0)
{
goto block_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Compiler_LCNF_anyExpr;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Compiler_LCNF_erasedExpr;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_instInhabitedExpr;
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__0), 7, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_25; uint8_t x_26; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_25 = lean_mk_string_unchecked("lcErased", 8, 8);
x_26 = lean_string_dec_eq(x_11, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_mk_string_unchecked("lcAny", 5, 5);
x_28 = lean_string_dec_eq(x_11, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_mk_string_unchecked("Decidable", 9, 9);
x_30 = lean_string_dec_eq(x_11, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_box(0);
lean_inc(x_11);
x_32 = l_Lean_Name_str___override(x_31, x_11);
lean_inc(x_7);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__1), 6, 3);
lean_closure_set(x_33, 0, x_9);
lean_closure_set(x_33, 1, x_32);
lean_closure_set(x_33, 2, x_7);
x_12 = x_33;
goto block_24;
}
else
{
lean_object* x_34; 
lean_dec(x_9);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__2___boxed), 3, 0);
x_12 = x_34;
goto block_24;
}
}
else
{
lean_object* x_35; 
lean_dec(x_9);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__3___boxed), 3, 0);
x_12 = x_35;
goto block_24;
}
}
else
{
lean_object* x_36; 
lean_dec(x_9);
lean_inc(x_2);
x_36 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__4___boxed), 4, 1);
lean_closure_set(x_36, 0, x_2);
x_12 = x_36;
goto block_24;
}
block_24:
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_apply_3(x_12, x_3, x_4, x_5);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = l_Lean_Name_str___override(x_16, x_11);
x_18 = l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__0(x_2, x_8, x_17, x_7, x_3, x_4, x_5);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l_Lean_Name_num___override(x_19, x_20);
x_22 = l_Lean_Name_str___override(x_21, x_11);
x_23 = l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__0(x_2, x_8, x_22, x_7, x_3, x_4, x_5);
return x_23;
}
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_9);
x_37 = l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__0(x_2, x_8, x_6, x_7, x_3, x_4, x_5);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_Compiler_LCNF_anyExpr;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toMonoType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_set(x_2, x_3, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_1 = x_7;
x_2 = x_9;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_toMonoType_visitApp(x_1, x_2, x_4, x_5, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Compiler_LCNF_toMonoType(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_mkArrow(x_8, x_2, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_headBeta(x_1);
switch (lean_obj_tag(x_5)) {
case 3:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Lean_Compiler_LCNF_erasedExpr;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = l_Lean_Compiler_LCNF_toMonoType_visitApp(x_5, x_9, x_2, x_3, x_4);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_box(0);
x_12 = l_Lean_Expr_sort___override(x_11);
x_13 = l_Lean_Expr_getAppNumArgs(x_5);
lean_inc(x_13);
x_14 = lean_mk_array(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
x_17 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_toMonoType_spec__0(x_5, x_14, x_16, x_2, x_3, x_4);
return x_17;
}
case 7:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 2);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Lean_Compiler_LCNF_anyExpr;
x_21 = lean_expr_instantiate1(x_19, x_20);
lean_dec(x_19);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Compiler_LCNF_toMonoType(x_21, x_2, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 4)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
x_29 = lean_box(0);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_22);
x_30 = l_Lean_Expr_const___override(x_29, x_28);
x_31 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_30, x_2, x_3, x_25);
lean_dec(x_30);
return x_31;
}
case 1:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_mk_string_unchecked("lcErased", 8, 8);
x_35 = lean_string_dec_eq(x_33, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_22);
x_36 = l_Lean_Name_str___override(x_29, x_33);
x_37 = l_Lean_Expr_const___override(x_36, x_28);
x_38 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_37, x_2, x_3, x_25);
lean_dec(x_37);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_39 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
case 1:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_22);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = l_Lean_Name_str___override(x_41, x_42);
x_44 = l_Lean_Name_str___override(x_43, x_40);
x_45 = l_Lean_Expr_const___override(x_44, x_28);
x_46 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_45, x_2, x_3, x_25);
lean_dec(x_45);
return x_46;
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_22);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_dec(x_27);
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_dec(x_32);
x_50 = l_Lean_Name_num___override(x_48, x_49);
x_51 = l_Lean_Name_str___override(x_50, x_47);
x_52 = l_Lean_Expr_const___override(x_51, x_28);
x_53 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_52, x_2, x_3, x_25);
lean_dec(x_52);
return x_53;
}
}
}
default: 
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_22);
x_54 = lean_ctor_get(x_27, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_27, 1);
lean_inc(x_55);
lean_dec(x_27);
x_56 = l_Lean_Name_num___override(x_54, x_55);
x_57 = l_Lean_Expr_const___override(x_56, x_28);
x_58 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_57, x_2, x_3, x_25);
lean_dec(x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_22, 1);
lean_inc(x_59);
lean_dec(x_22);
x_60 = lean_ctor_get(x_23, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_23, 1);
lean_inc(x_61);
x_62 = lean_box(0);
switch (lean_obj_tag(x_60)) {
case 0:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_Expr_const___override(x_62, x_61);
x_64 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_63, x_2, x_3, x_59);
lean_dec(x_63);
return x_64;
}
case 1:
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
switch (lean_obj_tag(x_65)) {
case 0:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = lean_mk_string_unchecked("lcErased", 8, 8);
x_68 = lean_string_dec_eq(x_66, x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = l_Lean_Name_str___override(x_62, x_66);
x_70 = l_Lean_Expr_const___override(x_69, x_61);
x_71 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_70, x_2, x_3, x_59);
lean_dec(x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_72 = l_Lean_Compiler_LCNF_erasedExpr;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_59);
return x_73;
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_dec(x_60);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_dec(x_65);
x_77 = l_Lean_Name_str___override(x_75, x_76);
x_78 = l_Lean_Name_str___override(x_77, x_74);
x_79 = l_Lean_Expr_const___override(x_78, x_61);
x_80 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_79, x_2, x_3, x_59);
lean_dec(x_79);
return x_80;
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_60, 1);
lean_inc(x_81);
lean_dec(x_60);
x_82 = lean_ctor_get(x_65, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_dec(x_65);
x_84 = l_Lean_Name_num___override(x_82, x_83);
x_85 = l_Lean_Name_str___override(x_84, x_81);
x_86 = l_Lean_Expr_const___override(x_85, x_61);
x_87 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_86, x_2, x_3, x_59);
lean_dec(x_86);
return x_87;
}
}
}
default: 
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_60, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_60, 1);
lean_inc(x_89);
lean_dec(x_60);
x_90 = l_Lean_Name_num___override(x_88, x_89);
x_91 = l_Lean_Expr_const___override(x_90, x_61);
x_92 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_91, x_2, x_3, x_59);
lean_dec(x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_22, 1);
lean_inc(x_93);
lean_dec(x_22);
lean_inc(x_23);
x_94 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_18, x_23, x_23, x_2, x_3, x_93);
lean_dec(x_23);
return x_94;
}
}
else
{
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
case 10:
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_5, 1);
lean_inc(x_95);
lean_dec(x_5);
x_1 = x_95;
goto _start;
}
default: 
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_97 = l_Lean_Compiler_LCNF_anyExpr;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_4);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_toMonoType_visitApp_spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_toMonoType_visitApp___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMonoType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_toMonoType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1659_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_Lean_Compiler_LCNF_CacheExtension_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_BaseTypes___hyg_3__spec__0(lean_box(0), x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Compiler_LCNF_monoTypeExt;
x_6 = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(x_5, x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_getOtherDeclBaseType(x_1, x_9, x_2, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_toMonoType(x_11, x_2, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instInhabitedExpr;
lean_inc(x_14);
x_17 = l_Lean_Compiler_LCNF_CacheExtension_insert___at___Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0(lean_box(0), x_16, x_5, x_1, x_14, x_2, x_3, x_15);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_6, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_BaseTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_BaseTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedTrivialStructureInfo);
l_Lean_Compiler_LCNF_instReprTrivialStructureInfo = _init_l_Lean_Compiler_LCNF_instReprTrivialStructureInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_instReprTrivialStructureInfo);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_MonoTypes___hyg_1659_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoTypeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoTypeExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
