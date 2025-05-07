// Lean compiler output
// Module: Lean.Compiler.LCNF.PrettyPrinter
// Imports: Lean.PrettyPrinter.Delaborator.Options Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.Internalize
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
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_explicit;
uint8_t l_Lean_Expr_isType0(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_all;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_pp_sanitizeNames;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_funBinderTypes;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_pp_letVarTypes;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1(uint8_t, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Std_Format_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_indentD(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_array_uget(x_14, x_4);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_7(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
lean_ctor_set_tag(x_16, 5);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 0, x_21);
x_22 = lean_mk_string_unchecked(" ", 1, 1);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_4, x_28);
x_4 = x_29;
x_5 = x_26;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_mk_string_unchecked("", 0, 0);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_mk_string_unchecked(" ", 1, 1);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_usize_of_nat(x_41);
x_43 = lean_usize_add(x_4, x_42);
x_4 = x_43;
x_5 = x_40;
x_11 = x_32;
goto _start;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_9);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_7(x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Array_toSubarray___redArg(x_1, x_18, x_10);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(x_2, x_19, x_21, x_23, x_16, x_3, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_19);
return x_24;
}
else
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Subarray_forInUnsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = lean_apply_7(x_1, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
lean_ctor_set_tag(x_16, 5);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 0, x_21);
lean_inc(x_21);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_2);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
lean_inc(x_21);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_6 = x_26;
x_12 = x_19;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_mk_string_unchecked("", 0, 0);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
lean_inc(x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_2);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
lean_inc(x_34);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_usize_of_nat(x_41);
x_43 = lean_usize_add(x_5, x_42);
x_5 = x_43;
x_6 = x_40;
x_12 = x_32;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = lean_array_size(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(x_3, x_1, x_2, x_11, x_13, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_getBinderName___redArg(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed), 1, 0);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_8, x_11, x_9);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed), 1, 0);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Name_toString(x_14, x_18, x_16);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_34; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
x_34 = l_Lean_Exception_isInterrupt(x_23);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isRuntime(x_23);
lean_dec(x_23);
x_25 = x_35;
goto block_33;
}
else
{
lean_dec(x_23);
x_25 = x_34;
goto block_33;
}
block_33:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_26 = lean_box(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Name_toString(x_1, x_29, x_27);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
else
{
lean_dec(x_24);
lean_dec(x_1);
return x_6;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_48; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
lean_inc(x_37);
lean_inc(x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_48 = l_Lean_Exception_isInterrupt(x_36);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Exception_isRuntime(x_36);
lean_dec(x_36);
x_39 = x_49;
goto block_47;
}
else
{
lean_dec(x_36);
x_39 = x_48;
goto block_47;
}
block_47:
{
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_38);
x_40 = lean_box(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_box(1);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_Name_toString(x_1, x_43, x_41);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
else
{
lean_dec(x_37);
lean_dec(x_1);
return x_38;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_1, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_8);
lean_inc(x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
lean_inc(x_8);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_8);
lean_inc(x_9);
x_15 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_10);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set(x_15, 6, x_12);
lean_ctor_set(x_15, 7, x_13);
lean_ctor_set(x_15, 8, x_14);
lean_inc(x_8);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_8);
lean_inc(x_8);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_8);
lean_inc(x_8);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_8);
lean_inc(x_8);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_8);
lean_inc(x_19);
lean_inc(x_16);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_19);
lean_ctor_set(x_20, 5, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_unsigned_to_nat(5u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_nat_pow(x_21, x_24);
lean_dec(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = lean_usize_to_nat(x_26);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_dec(x_27);
lean_inc(x_28);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_7);
lean_ctor_set(x_30, 3, x_7);
lean_ctor_set_usize(x_30, 4, x_23);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_8);
lean_inc_n(x_9, 2);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_9);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_6);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_mk_ref(x_33, x_5);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(1);
x_38 = lean_box(1);
x_39 = lean_box(0);
x_40 = lean_box(2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 0, 18);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, 0, x_43);
x_44 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, 1, x_44);
x_45 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, 2, x_45);
x_46 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, 3, x_46);
x_47 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, 4, x_47);
x_48 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 5, x_48);
x_49 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 6, x_49);
x_50 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, 7, x_50);
x_51 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 8, x_51);
x_52 = lean_unbox(x_38);
lean_ctor_set_uint8(x_42, 9, x_52);
x_53 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, 10, x_53);
x_54 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 11, x_54);
x_55 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 12, x_55);
x_56 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 13, x_56);
x_57 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, 14, x_57);
x_58 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 15, x_58);
x_59 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 16, x_59);
x_60 = lean_unbox(x_37);
lean_ctor_set_uint8(x_42, 17, x_60);
x_61 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_42);
x_62 = lean_mk_empty_array_with_capacity(x_7);
x_63 = lean_box(0);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_6);
lean_ctor_set(x_65, 2, x_2);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_7);
lean_ctor_set(x_65, 6, x_64);
lean_ctor_set_uint64(x_65, sizeof(void*)*7, x_61);
x_66 = lean_unbox(x_41);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 8, x_66);
x_67 = lean_unbox(x_41);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 9, x_67);
x_68 = lean_unbox(x_41);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 10, x_68);
x_69 = l_Lean_Meta_ppExpr(x_1, x_65, x_35, x_3, x_4, x_36);
lean_dec(x_65);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_35, x_71);
lean_dec(x_35);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_mk_string_unchecked("◾", 3, 1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_10, x_3, x_4, x_5, x_6);
return x_11;
}
default: 
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_4, 2);
x_15 = l_Lean_pp_explicit;
x_16 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_2);
x_17 = lean_mk_string_unchecked("_", 1, 1);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isConst(x_13);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isProp(x_13);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_isType0(x_13);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_isFVar(x_13);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_4, x_5, x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_mk_string_unchecked("(", 1, 1);
x_27 = lean_mk_string_unchecked(")", 1, 1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_to_int(x_28);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_26);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_25);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_mk_string_unchecked("(", 1, 1);
x_40 = lean_mk_string_unchecked(")", 1, 1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_to_int(x_41);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_39);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_40);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_38);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_free_object(x_1);
x_51 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_4, x_5, x_6);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_free_object(x_1);
x_52 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_4, x_5, x_6);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_free_object(x_1);
x_53 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_4, x_5, x_6);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_free_object(x_1);
x_54 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_4, x_5, x_6);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_4, 2);
x_57 = l_Lean_pp_explicit;
x_58 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
lean_dec(x_2);
x_59 = lean_mk_string_unchecked("_", 1, 1);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_6);
return x_61;
}
else
{
uint8_t x_62; 
x_62 = l_Lean_Expr_isConst(x_55);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Expr_isProp(x_55);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_Expr_isType0(x_55);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Expr_isFVar(x_55);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_66 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_55, x_2, x_4, x_5, x_6);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_mk_string_unchecked("(", 1, 1);
x_71 = lean_mk_string_unchecked(")", 1, 1);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_to_int(x_72);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_70);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_67);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
if (lean_is_scalar(x_69)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_69;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_68);
return x_82;
}
else
{
lean_object* x_83; 
x_83 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_55, x_2, x_4, x_5, x_6);
return x_83;
}
}
else
{
lean_object* x_84; 
x_84 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_55, x_2, x_4, x_5, x_6);
return x_84;
}
}
else
{
lean_object* x_85; 
x_85 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_55, x_2, x_4, x_5, x_6);
return x_85;
}
}
else
{
lean_object* x_86; 
x_86 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_55, x_2, x_4, x_5, x_6);
return x_86;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppArg___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_ppArg___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked(" ", 1, 1);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 7, 0);
x_11 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_LitValue_toExpr(x_8);
x_10 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_9, x_2, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_mk_string_unchecked("◾", 3, 1);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_15, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_20);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_mk_string_unchecked(" # ", 3, 3);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_32);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_mk_string_unchecked(" # ", 3, 3);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
}
else
{
lean_dec(x_14);
return x_16;
}
}
case 3:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_Expr_const___override(x_42, x_43);
lean_inc(x_2);
x_46 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_45, x_2, x_5, x_6, x_7);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = l_Lean_Compiler_LCNF_PP_ppArgs(x_44, x_2, x_3, x_4, x_5, x_6, x_49);
lean_dec(x_44);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_mk_string_unchecked("", 0, 0);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_54);
lean_ctor_set_tag(x_46, 5);
lean_ctor_set(x_46, 1, x_48);
lean_ctor_set(x_46, 0, x_54);
lean_inc(x_54);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_mk_string_unchecked("", 0, 0);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_61);
lean_ctor_set_tag(x_46, 5);
lean_ctor_set(x_46, 1, x_48);
lean_ctor_set(x_46, 0, x_61);
lean_inc(x_61);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
else
{
lean_free_object(x_46);
lean_dec(x_48);
return x_50;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_46, 0);
x_67 = lean_ctor_get(x_46, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_46);
x_68 = l_Lean_Compiler_LCNF_PP_ppArgs(x_44, x_2, x_3, x_4, x_5, x_6, x_67);
lean_dec(x_44);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_mk_string_unchecked("", 0, 0);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_inc(x_73);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
lean_inc(x_73);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
if (lean_is_scalar(x_71)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_71;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
return x_78;
}
else
{
lean_dec(x_66);
return x_68;
}
}
}
default: 
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_1, 1);
x_82 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_80, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
x_86 = l_Lean_Compiler_LCNF_PP_ppArgs(x_81, x_2, x_3, x_4, x_5, x_6, x_85);
lean_dec(x_81);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_mk_string_unchecked("", 0, 0);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_inc(x_90);
lean_ctor_set_tag(x_82, 5);
lean_ctor_set(x_82, 1, x_84);
lean_ctor_set(x_82, 0, x_90);
lean_inc(x_90);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_82);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_88);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_86, 0, x_92);
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_ctor_get(x_86, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_86);
x_95 = lean_mk_string_unchecked("", 0, 0);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_inc(x_96);
lean_ctor_set_tag(x_82, 5);
lean_ctor_set(x_82, 1, x_84);
lean_ctor_set(x_82, 0, x_96);
lean_inc(x_96);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_96);
lean_ctor_set(x_1, 0, x_82);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_93);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
else
{
lean_free_object(x_82);
lean_dec(x_84);
lean_free_object(x_1);
return x_86;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_82, 0);
x_101 = lean_ctor_get(x_82, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_82);
x_102 = l_Lean_Compiler_LCNF_PP_ppArgs(x_81, x_2, x_3, x_4, x_5, x_6, x_101);
lean_dec(x_81);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_mk_string_unchecked("", 0, 0);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
lean_inc(x_107);
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
lean_inc(x_107);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_107);
lean_ctor_set(x_1, 0, x_108);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_103);
x_110 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
if (lean_is_scalar(x_105)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_105;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_104);
return x_111;
}
else
{
lean_dec(x_100);
lean_free_object(x_1);
return x_102;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_81);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_82;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_1, 0);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_1);
x_114 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_112, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = l_Lean_Compiler_LCNF_PP_ppArgs(x_113, x_2, x_3, x_4, x_5, x_6, x_116);
lean_dec(x_113);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_mk_string_unchecked("", 0, 0);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
lean_inc(x_123);
if (lean_is_scalar(x_117)) {
 x_124 = lean_alloc_ctor(5, 2, 0);
} else {
 x_124 = x_117;
 lean_ctor_set_tag(x_124, 5);
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_115);
lean_inc(x_123);
x_125 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_119);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_123);
if (lean_is_scalar(x_121)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_121;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_120);
return x_128;
}
else
{
lean_dec(x_117);
lean_dec(x_115);
return x_118;
}
}
else
{
lean_dec(x_113);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_114;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_80; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed), 1, 0);
x_80 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_mk_string_unchecked("", 0, 0);
x_7 = x_81;
goto block_79;
}
else
{
lean_object* x_82; 
x_82 = lean_mk_string_unchecked("@&", 2, 2);
x_7 = x_82;
goto block_79;
}
block_79:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_pp_funBinderTypes;
x_10 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_2);
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Name_toString(x_13, x_15, x_12);
x_17 = lean_string_append(x_7, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_20, x_2, x_3, x_4, x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_mk_string_unchecked("", 0, 0);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_Name_toString(x_26, x_10, x_6);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_25);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked(" : ", 3, 3);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_7);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_25);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
x_38 = lean_mk_string_unchecked("(", 1, 1);
x_39 = lean_mk_string_unchecked(")", 1, 1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_to_int(x_40);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_38);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
lean_ctor_set(x_21, 0, x_48);
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_mk_string_unchecked("", 0, 0);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
x_55 = l_Lean_Name_toString(x_54, x_10, x_6);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_inc(x_53);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked(" : ", 3, 3);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_7);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_53);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_50);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_53);
x_66 = lean_mk_string_unchecked("(", 1, 1);
x_67 = lean_mk_string_unchecked(")", 1, 1);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_to_int(x_68);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_66);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_76, 0, x_74);
x_77 = lean_unbox(x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_77);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_51);
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppParam___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_PP_ppParam___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked(" ", 1, 1);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 7, 0);
x_11 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = l_Lean_pp_letVarTypes;
x_10 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_PP_ppLetValue(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(x_10);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("let ", 4, 4);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Name_toString(x_19, x_21, x_16);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked(" := ", 4, 4);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_14);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_box(x_10);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_mk_string_unchecked("let ", 4, 4);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
x_41 = l_Lean_Name_toString(x_38, x_40, x_35);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked(" := ", 4, 4);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_32);
x_48 = lean_mk_string_unchecked("", 0, 0);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_33);
return x_51;
}
}
else
{
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
lean_inc(x_2);
x_53 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_52, x_2, x_5, x_6, x_7);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_ctor_get(x_1, 3);
lean_inc(x_57);
x_58 = l_Lean_Compiler_LCNF_PP_ppLetValue(x_57, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed), 1, 0);
x_62 = lean_mk_string_unchecked("let ", 4, 4);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l_Lean_Name_toString(x_64, x_10, x_61);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set_tag(x_53, 5);
lean_ctor_set(x_53, 1, x_66);
lean_ctor_set(x_53, 0, x_63);
x_67 = lean_mk_string_unchecked(" : ", 3, 3);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_55);
x_71 = lean_mk_string_unchecked(" := ", 4, 4);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_58, 0, x_77);
return x_58;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_78 = lean_ctor_get(x_58, 0);
x_79 = lean_ctor_get(x_58, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_58);
x_80 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed), 1, 0);
x_81 = lean_mk_string_unchecked("let ", 4, 4);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec(x_1);
x_84 = l_Lean_Name_toString(x_83, x_10, x_80);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_tag(x_53, 5);
lean_ctor_set(x_53, 1, x_85);
lean_ctor_set(x_53, 0, x_82);
x_86 = lean_mk_string_unchecked(" : ", 3, 3);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_53);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_55);
x_90 = lean_mk_string_unchecked(" := ", 4, 4);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_78);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_79);
return x_97;
}
}
else
{
lean_free_object(x_53);
lean_dec(x_55);
lean_dec(x_1);
return x_58;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_53, 0);
x_99 = lean_ctor_get(x_53, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_53);
x_100 = lean_ctor_get(x_1, 3);
lean_inc(x_100);
x_101 = l_Lean_Compiler_LCNF_PP_ppLetValue(x_100, x_2, x_3, x_4, x_5, x_6, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed), 1, 0);
x_106 = lean_mk_string_unchecked("let ", 4, 4);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
lean_dec(x_1);
x_109 = l_Lean_Name_toString(x_108, x_10, x_105);
x_110 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_mk_string_unchecked(" : ", 3, 3);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_98);
x_116 = lean_mk_string_unchecked(" := ", 4, 4);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_102);
x_120 = lean_mk_string_unchecked("", 0, 0);
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
if (lean_is_scalar(x_104)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_104;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_103);
return x_123;
}
else
{
lean_dec(x_98);
lean_dec(x_1);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Expr_isErased(x_2);
if (x_6 == 0)
{
size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0(x_7, x_9, x_1);
x_11 = l_Lean_Compiler_LCNF_instantiateForall(x_2, x_10, x_3, x_4, x_5);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_PP_getFunType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Compiler_LCNF_PP_ppParams(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_PP_getFunType(x_8, x_13, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_15, x_2, x_5, x_6, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
x_22 = l_Lean_Compiler_LCNF_PP_ppCode(x_21, x_2, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed), 1, 0);
x_26 = lean_mk_string_unchecked("", 0, 0);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Name_toString(x_28, x_30, x_25);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_27);
lean_ctor_set_tag(x_17, 5);
lean_ctor_set(x_17, 1, x_32);
lean_ctor_set(x_17, 0, x_27);
lean_inc(x_27);
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_27);
lean_ctor_set(x_9, 0, x_17);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_11);
x_34 = lean_mk_string_unchecked(" : ", 3, 3);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_19);
x_38 = lean_mk_string_unchecked(" :=", 3, 3);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Std_Format_indentD(x_24);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
lean_ctor_set(x_22, 0, x_43);
return x_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed), 1, 0);
x_47 = lean_mk_string_unchecked("", 0, 0);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_box(1);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_Name_toString(x_49, x_51, x_46);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_48);
lean_ctor_set_tag(x_17, 5);
lean_ctor_set(x_17, 1, x_53);
lean_ctor_set(x_17, 0, x_48);
lean_inc(x_48);
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_48);
lean_ctor_set(x_9, 0, x_17);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_9);
lean_ctor_set(x_54, 1, x_11);
x_55 = lean_mk_string_unchecked(" : ", 3, 3);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_19);
x_59 = lean_mk_string_unchecked(" :=", 3, 3);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Std_Format_indentD(x_44);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_45);
return x_65;
}
}
else
{
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_1);
return x_22;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_17, 0);
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_17);
x_68 = lean_ctor_get(x_1, 4);
lean_inc(x_68);
x_69 = l_Lean_Compiler_LCNF_PP_ppCode(x_68, x_2, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed), 1, 0);
x_74 = lean_mk_string_unchecked("", 0, 0);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_box(1);
x_78 = lean_unbox(x_77);
x_79 = l_Lean_Name_toString(x_76, x_78, x_73);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_inc(x_75);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_75);
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_75);
lean_ctor_set(x_9, 0, x_81);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_9);
lean_ctor_set(x_82, 1, x_11);
x_83 = lean_mk_string_unchecked(" : ", 3, 3);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_66);
x_87 = lean_mk_string_unchecked(" :=", 3, 3);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Std_Format_indentD(x_70);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_75);
if (lean_is_scalar(x_72)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_72;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_71);
return x_93;
}
else
{
lean_dec(x_66);
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_1);
return x_69;
}
}
}
else
{
uint8_t x_94; 
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_14);
if (x_94 == 0)
{
return x_14;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_14, 0);
x_96 = lean_ctor_get(x_14, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_14);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_9, 0);
x_99 = lean_ctor_get(x_9, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_9);
x_100 = lean_ctor_get(x_1, 3);
lean_inc(x_100);
x_101 = l_Lean_Compiler_LCNF_PP_getFunType(x_8, x_100, x_5, x_6, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_2);
x_104 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_102, x_2, x_5, x_6, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_1, 4);
lean_inc(x_108);
x_109 = l_Lean_Compiler_LCNF_PP_ppCode(x_108, x_2, x_3, x_4, x_5, x_6, x_106);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed), 1, 0);
x_114 = lean_mk_string_unchecked("", 0, 0);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_ctor_get(x_1, 1);
lean_inc(x_116);
lean_dec(x_1);
x_117 = lean_box(1);
x_118 = lean_unbox(x_117);
x_119 = l_Lean_Name_toString(x_116, x_118, x_113);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
lean_inc(x_115);
if (lean_is_scalar(x_107)) {
 x_121 = lean_alloc_ctor(5, 2, 0);
} else {
 x_121 = x_107;
 lean_ctor_set_tag(x_121, 5);
}
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_120);
lean_inc(x_115);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_115);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_98);
x_124 = lean_mk_string_unchecked(" : ", 3, 3);
x_125 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_105);
x_128 = lean_mk_string_unchecked(" :=", 3, 3);
x_129 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Std_Format_indentD(x_110);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_115);
if (lean_is_scalar(x_112)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_112;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_111);
return x_134;
}
else
{
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_98);
lean_dec(x_1);
return x_109;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_98);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_ctor_get(x_101, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_101, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_137 = x_101;
} else {
 lean_dec_ref(x_101);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Compiler_LCNF_PP_ppLetDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Compiler_LCNF_PP_ppCode(x_10, x_2, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_mk_string_unchecked(";", 1, 1);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_11, 5);
lean_ctor_set(x_11, 1, x_19);
x_20 = lean_box(1);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_11);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_mk_string_unchecked(";", 1, 1);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_tag(x_11, 5);
lean_ctor_set(x_11, 1, x_25);
x_26 = lean_box(1);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_11);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
lean_free_object(x_11);
lean_dec(x_13);
lean_free_object(x_1);
return x_15;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = l_Lean_Compiler_LCNF_PP_ppCode(x_10, x_2, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_mk_string_unchecked(";", 1, 1);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(1);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_32);
if (lean_is_scalar(x_34)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_34;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
else
{
lean_dec(x_29);
lean_free_object(x_1);
return x_31;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = l_Lean_Compiler_LCNF_PP_ppLetDecl(x_41, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = l_Lean_Compiler_LCNF_PP_ppCode(x_42, x_2, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_mk_string_unchecked(";", 1, 1);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
if (lean_is_scalar(x_46)) {
 x_53 = lean_alloc_ctor(5, 2, 0);
} else {
 x_53 = x_46;
 lean_ctor_set_tag(x_53, 5);
}
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
if (lean_is_scalar(x_50)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_50;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
else
{
lean_dec(x_46);
lean_dec(x_44);
return x_47;
}
}
else
{
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
}
}
case 1:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_59, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = l_Lean_Compiler_LCNF_PP_ppCode(x_60, x_2, x_3, x_4, x_5, x_6, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_mk_string_unchecked("fun ", 4, 4);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_tag(x_61, 5);
lean_ctor_set(x_61, 1, x_63);
lean_ctor_set(x_61, 0, x_69);
x_70 = lean_mk_string_unchecked(";", 1, 1);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_61);
x_72 = lean_box(1);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_65, 0, x_74);
return x_65;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_65, 0);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_65);
x_77 = lean_mk_string_unchecked("fun ", 4, 4);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_tag(x_61, 5);
lean_ctor_set(x_61, 1, x_63);
lean_ctor_set(x_61, 0, x_78);
x_79 = lean_mk_string_unchecked(";", 1, 1);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_80);
lean_ctor_set(x_1, 0, x_61);
x_81 = lean_box(1);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
return x_84;
}
}
else
{
lean_free_object(x_61);
lean_dec(x_63);
lean_free_object(x_1);
return x_65;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_61, 0);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_61);
x_87 = l_Lean_Compiler_LCNF_PP_ppCode(x_60, x_2, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_mk_string_unchecked("fun ", 4, 4);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_85);
x_94 = lean_mk_string_unchecked(";", 1, 1);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_95);
lean_ctor_set(x_1, 0, x_93);
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_90;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_89);
return x_99;
}
else
{
lean_dec(x_85);
lean_free_object(x_1);
return x_87;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_61;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_1, 0);
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_102 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_100, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Compiler_LCNF_PP_ppCode(x_101, x_2, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_mk_string_unchecked("fun ", 4, 4);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
if (lean_is_scalar(x_105)) {
 x_112 = lean_alloc_ctor(5, 2, 0);
} else {
 x_112 = x_105;
 lean_ctor_set_tag(x_112, 5);
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_103);
x_113 = lean_mk_string_unchecked(";", 1, 1);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_box(1);
x_117 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_107);
if (lean_is_scalar(x_109)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_109;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_108);
return x_119;
}
else
{
lean_dec(x_105);
lean_dec(x_103);
return x_106;
}
}
else
{
lean_dec(x_101);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_102;
}
}
}
case 2:
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_1);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_1, 0);
x_122 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_123 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_121, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
x_127 = l_Lean_Compiler_LCNF_PP_ppCode(x_122, x_2, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_mk_string_unchecked("jp ", 3, 3);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set_tag(x_123, 5);
lean_ctor_set(x_123, 1, x_125);
lean_ctor_set(x_123, 0, x_131);
x_132 = lean_mk_string_unchecked(";", 1, 1);
x_133 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_133);
lean_ctor_set(x_1, 0, x_123);
x_134 = lean_box(1);
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_129);
lean_ctor_set(x_127, 0, x_136);
return x_127;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_127, 0);
x_138 = lean_ctor_get(x_127, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_127);
x_139 = lean_mk_string_unchecked("jp ", 3, 3);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set_tag(x_123, 5);
lean_ctor_set(x_123, 1, x_125);
lean_ctor_set(x_123, 0, x_140);
x_141 = lean_mk_string_unchecked(";", 1, 1);
x_142 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_142);
lean_ctor_set(x_1, 0, x_123);
x_143 = lean_box(1);
x_144 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_138);
return x_146;
}
}
else
{
lean_free_object(x_123);
lean_dec(x_125);
lean_free_object(x_1);
return x_127;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_123, 0);
x_148 = lean_ctor_get(x_123, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_123);
x_149 = l_Lean_Compiler_LCNF_PP_ppCode(x_122, x_2, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_mk_string_unchecked("jp ", 3, 3);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_147);
x_156 = lean_mk_string_unchecked(";", 1, 1);
x_157 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_157);
lean_ctor_set(x_1, 0, x_155);
x_158 = lean_box(1);
x_159 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_159, 0, x_1);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_150);
if (lean_is_scalar(x_152)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_152;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_151);
return x_161;
}
else
{
lean_dec(x_147);
lean_free_object(x_1);
return x_149;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_122);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_123;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_1, 0);
x_163 = lean_ctor_get(x_1, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_164 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_162, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = l_Lean_Compiler_LCNF_PP_ppCode(x_163, x_2, x_3, x_4, x_5, x_6, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_mk_string_unchecked("jp ", 3, 3);
x_173 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_173, 0, x_172);
if (lean_is_scalar(x_167)) {
 x_174 = lean_alloc_ctor(5, 2, 0);
} else {
 x_174 = x_167;
 lean_ctor_set_tag(x_174, 5);
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_165);
x_175 = lean_mk_string_unchecked(";", 1, 1);
x_176 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_box(1);
x_179 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_169);
if (lean_is_scalar(x_171)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_171;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_170);
return x_181;
}
else
{
lean_dec(x_167);
lean_dec(x_165);
return x_168;
}
}
else
{
lean_dec(x_163);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_164;
}
}
}
case 3:
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_1);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_1, 0);
x_184 = lean_ctor_get(x_1, 1);
x_185 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_183, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = l_Lean_Compiler_LCNF_PP_ppArgs(x_184, x_2, x_3, x_4, x_5, x_6, x_188);
lean_dec(x_184);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_mk_string_unchecked("goto ", 5, 5);
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set_tag(x_185, 5);
lean_ctor_set(x_185, 1, x_187);
lean_ctor_set(x_185, 0, x_193);
x_194 = lean_mk_string_unchecked("", 0, 0);
x_195 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_195, 0, x_194);
lean_inc(x_195);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_195);
lean_ctor_set(x_1, 0, x_185);
x_196 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_191);
x_197 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
lean_ctor_set(x_189, 0, x_197);
return x_189;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_198 = lean_ctor_get(x_189, 0);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_189);
x_200 = lean_mk_string_unchecked("goto ", 5, 5);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set_tag(x_185, 5);
lean_ctor_set(x_185, 1, x_187);
lean_ctor_set(x_185, 0, x_201);
x_202 = lean_mk_string_unchecked("", 0, 0);
x_203 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_203, 0, x_202);
lean_inc(x_203);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_203);
lean_ctor_set(x_1, 0, x_185);
x_204 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_204, 0, x_1);
lean_ctor_set(x_204, 1, x_198);
x_205 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_199);
return x_206;
}
}
else
{
lean_free_object(x_185);
lean_dec(x_187);
lean_free_object(x_1);
return x_189;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_185, 0);
x_208 = lean_ctor_get(x_185, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_185);
x_209 = l_Lean_Compiler_LCNF_PP_ppArgs(x_184, x_2, x_3, x_4, x_5, x_6, x_208);
lean_dec(x_184);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_mk_string_unchecked("goto ", 5, 5);
x_214 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_207);
x_216 = lean_mk_string_unchecked("", 0, 0);
x_217 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_217, 0, x_216);
lean_inc(x_217);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_217);
lean_ctor_set(x_1, 0, x_215);
x_218 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_218, 0, x_1);
lean_ctor_set(x_218, 1, x_210);
x_219 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
if (lean_is_scalar(x_212)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_212;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_211);
return x_220;
}
else
{
lean_dec(x_207);
lean_free_object(x_1);
return x_209;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_185;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_1, 0);
x_222 = lean_ctor_get(x_1, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_1);
x_223 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_221, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = l_Lean_Compiler_LCNF_PP_ppArgs(x_222, x_2, x_3, x_4, x_5, x_6, x_225);
lean_dec(x_222);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = lean_mk_string_unchecked("goto ", 5, 5);
x_232 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_232, 0, x_231);
if (lean_is_scalar(x_226)) {
 x_233 = lean_alloc_ctor(5, 2, 0);
} else {
 x_233 = x_226;
 lean_ctor_set_tag(x_233, 5);
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_224);
x_234 = lean_mk_string_unchecked("", 0, 0);
x_235 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_235, 0, x_234);
lean_inc(x_235);
x_236 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_228);
x_238 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
if (lean_is_scalar(x_230)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_230;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_229);
return x_239;
}
else
{
lean_dec(x_226);
lean_dec(x_224);
return x_227;
}
}
else
{
lean_dec(x_222);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_223;
}
}
}
case 4:
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_1);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_1, 0);
x_242 = lean_ctor_get(x_241, 2);
lean_inc(x_242);
x_243 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_242, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_243) == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_ctor_get(x_243, 1);
x_247 = lean_ctor_get(x_241, 1);
lean_inc(x_247);
lean_inc(x_2);
x_248 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_247, x_2, x_5, x_6, x_246);
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_250 = lean_ctor_get(x_248, 0);
x_251 = lean_ctor_get(x_248, 1);
x_252 = lean_box(1);
x_253 = lean_ctor_get(x_241, 3);
lean_inc(x_253);
lean_dec(x_241);
x_254 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt), 7, 0);
x_255 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_252, x_253, x_254, x_2, x_3, x_4, x_5, x_6, x_251);
lean_dec(x_253);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = lean_mk_string_unchecked("cases ", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_tag(x_248, 5);
lean_ctor_set(x_248, 1, x_245);
lean_ctor_set(x_248, 0, x_1);
x_259 = lean_mk_string_unchecked(" : ", 3, 3);
x_260 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set_tag(x_243, 5);
lean_ctor_set(x_243, 1, x_260);
lean_ctor_set(x_243, 0, x_248);
x_261 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_261, 0, x_243);
lean_ctor_set(x_261, 1, x_250);
x_262 = lean_mk_string_unchecked("", 0, 0);
x_263 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_263, 0, x_262);
lean_inc(x_263);
x_264 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_257);
x_266 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_263);
lean_ctor_set(x_255, 0, x_266);
return x_255;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_267 = lean_ctor_get(x_255, 0);
x_268 = lean_ctor_get(x_255, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_255);
x_269 = lean_mk_string_unchecked("cases ", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_tag(x_248, 5);
lean_ctor_set(x_248, 1, x_245);
lean_ctor_set(x_248, 0, x_1);
x_270 = lean_mk_string_unchecked(" : ", 3, 3);
x_271 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set_tag(x_243, 5);
lean_ctor_set(x_243, 1, x_271);
lean_ctor_set(x_243, 0, x_248);
x_272 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_272, 0, x_243);
lean_ctor_set(x_272, 1, x_250);
x_273 = lean_mk_string_unchecked("", 0, 0);
x_274 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_274, 0, x_273);
lean_inc(x_274);
x_275 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_267);
x_277 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_268);
return x_278;
}
}
else
{
lean_free_object(x_248);
lean_dec(x_250);
lean_free_object(x_243);
lean_dec(x_245);
lean_free_object(x_1);
return x_255;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_279 = lean_ctor_get(x_248, 0);
x_280 = lean_ctor_get(x_248, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_248);
x_281 = lean_box(1);
x_282 = lean_ctor_get(x_241, 3);
lean_inc(x_282);
lean_dec(x_241);
x_283 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt), 7, 0);
x_284 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_281, x_282, x_283, x_2, x_3, x_4, x_5, x_6, x_280);
lean_dec(x_282);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
x_288 = lean_mk_string_unchecked("cases ", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_288);
x_289 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_289, 0, x_1);
lean_ctor_set(x_289, 1, x_245);
x_290 = lean_mk_string_unchecked(" : ", 3, 3);
x_291 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set_tag(x_243, 5);
lean_ctor_set(x_243, 1, x_291);
lean_ctor_set(x_243, 0, x_289);
x_292 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_292, 0, x_243);
lean_ctor_set(x_292, 1, x_279);
x_293 = lean_mk_string_unchecked("", 0, 0);
x_294 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_294, 0, x_293);
lean_inc(x_294);
x_295 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_285);
x_297 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_294);
if (lean_is_scalar(x_287)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_287;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_286);
return x_298;
}
else
{
lean_dec(x_279);
lean_free_object(x_243);
lean_dec(x_245);
lean_free_object(x_1);
return x_284;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_299 = lean_ctor_get(x_243, 0);
x_300 = lean_ctor_get(x_243, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_243);
x_301 = lean_ctor_get(x_241, 1);
lean_inc(x_301);
lean_inc(x_2);
x_302 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_301, x_2, x_5, x_6, x_300);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
x_306 = lean_box(1);
x_307 = lean_ctor_get(x_241, 3);
lean_inc(x_307);
lean_dec(x_241);
x_308 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt), 7, 0);
x_309 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_306, x_307, x_308, x_2, x_3, x_4, x_5, x_6, x_304);
lean_dec(x_307);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_313 = lean_mk_string_unchecked("cases ", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_313);
if (lean_is_scalar(x_305)) {
 x_314 = lean_alloc_ctor(5, 2, 0);
} else {
 x_314 = x_305;
 lean_ctor_set_tag(x_314, 5);
}
lean_ctor_set(x_314, 0, x_1);
lean_ctor_set(x_314, 1, x_299);
x_315 = lean_mk_string_unchecked(" : ", 3, 3);
x_316 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_303);
x_319 = lean_mk_string_unchecked("", 0, 0);
x_320 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_320, 0, x_319);
lean_inc(x_320);
x_321 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_310);
x_323 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_320);
if (lean_is_scalar(x_312)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_312;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_311);
return x_324;
}
else
{
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_299);
lean_free_object(x_1);
return x_309;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_241);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_243;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_1, 0);
lean_inc(x_325);
lean_dec(x_1);
x_326 = lean_ctor_get(x_325, 2);
lean_inc(x_326);
x_327 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_326, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_330 = x_327;
} else {
 lean_dec_ref(x_327);
 x_330 = lean_box(0);
}
x_331 = lean_ctor_get(x_325, 1);
lean_inc(x_331);
lean_inc(x_2);
x_332 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_331, x_2, x_5, x_6, x_329);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_335 = x_332;
} else {
 lean_dec_ref(x_332);
 x_335 = lean_box(0);
}
x_336 = lean_box(1);
x_337 = lean_ctor_get(x_325, 3);
lean_inc(x_337);
lean_dec(x_325);
x_338 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt), 7, 0);
x_339 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_336, x_337, x_338, x_2, x_3, x_4, x_5, x_6, x_334);
lean_dec(x_337);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_342 = x_339;
} else {
 lean_dec_ref(x_339);
 x_342 = lean_box(0);
}
x_343 = lean_mk_string_unchecked("cases ", 6, 6);
x_344 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_344, 0, x_343);
if (lean_is_scalar(x_335)) {
 x_345 = lean_alloc_ctor(5, 2, 0);
} else {
 x_345 = x_335;
 lean_ctor_set_tag(x_345, 5);
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_328);
x_346 = lean_mk_string_unchecked(" : ", 3, 3);
x_347 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_347, 0, x_346);
if (lean_is_scalar(x_330)) {
 x_348 = lean_alloc_ctor(5, 2, 0);
} else {
 x_348 = x_330;
 lean_ctor_set_tag(x_348, 5);
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_333);
x_350 = lean_mk_string_unchecked("", 0, 0);
x_351 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_351, 0, x_350);
lean_inc(x_351);
x_352 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_340);
x_354 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_351);
if (lean_is_scalar(x_342)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_342;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_341);
return x_355;
}
else
{
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_330);
lean_dec(x_328);
return x_339;
}
}
else
{
lean_dec(x_325);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_327;
}
}
}
case 5:
{
uint8_t x_356; 
lean_dec(x_3);
lean_dec(x_2);
x_356 = !lean_is_exclusive(x_1);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_1, 0);
x_358 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_357, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
x_359 = !lean_is_exclusive(x_358);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_360 = lean_ctor_get(x_358, 0);
x_361 = lean_mk_string_unchecked("return ", 7, 7);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_361);
x_362 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_362, 0, x_1);
lean_ctor_set(x_362, 1, x_360);
x_363 = lean_mk_string_unchecked("", 0, 0);
x_364 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_364, 0, x_363);
x_365 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_364);
lean_ctor_set(x_358, 0, x_365);
return x_358;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_366 = lean_ctor_get(x_358, 0);
x_367 = lean_ctor_get(x_358, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_358);
x_368 = lean_mk_string_unchecked("return ", 7, 7);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_368);
x_369 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_369, 0, x_1);
lean_ctor_set(x_369, 1, x_366);
x_370 = lean_mk_string_unchecked("", 0, 0);
x_371 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_371, 0, x_370);
x_372 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_367);
return x_373;
}
}
else
{
lean_free_object(x_1);
return x_358;
}
}
else
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_1, 0);
lean_inc(x_374);
lean_dec(x_1);
x_375 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_374, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
x_379 = lean_mk_string_unchecked("return ", 7, 7);
x_380 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_380, 0, x_379);
x_381 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_376);
x_382 = lean_mk_string_unchecked("", 0, 0);
x_383 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_383, 0, x_382);
x_384 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_383);
if (lean_is_scalar(x_378)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_378;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_377);
return x_385;
}
else
{
return x_375;
}
}
}
default: 
{
uint8_t x_386; 
lean_dec(x_4);
lean_dec(x_3);
x_386 = !lean_is_exclusive(x_1);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_387 = lean_ctor_get(x_1, 0);
x_388 = lean_ctor_get(x_5, 2);
lean_inc(x_388);
x_389 = l_Lean_pp_all;
x_390 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_388, x_389);
lean_dec(x_388);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_387);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_391 = lean_mk_string_unchecked("⊥", 3, 1);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_391);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_1);
lean_ctor_set(x_392, 1, x_7);
return x_392;
}
else
{
lean_object* x_393; uint8_t x_394; 
x_393 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_387, x_2, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_394 = !lean_is_exclusive(x_393);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_395 = lean_ctor_get(x_393, 0);
x_396 = lean_mk_string_unchecked("⊥ : ", 6, 4);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_396);
x_397 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_397, 0, x_1);
lean_ctor_set(x_397, 1, x_395);
x_398 = lean_mk_string_unchecked("", 0, 0);
x_399 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_399, 0, x_398);
x_400 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_399);
lean_ctor_set(x_393, 0, x_400);
return x_393;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_401 = lean_ctor_get(x_393, 0);
x_402 = lean_ctor_get(x_393, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_393);
x_403 = lean_mk_string_unchecked("⊥ : ", 6, 4);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_403);
x_404 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_404, 0, x_1);
lean_ctor_set(x_404, 1, x_401);
x_405 = lean_mk_string_unchecked("", 0, 0);
x_406 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_402);
return x_408;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_409 = lean_ctor_get(x_1, 0);
lean_inc(x_409);
lean_dec(x_1);
x_410 = lean_ctor_get(x_5, 2);
lean_inc(x_410);
x_411 = l_Lean_pp_all;
x_412 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_410, x_411);
lean_dec(x_410);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_409);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_413 = lean_mk_string_unchecked("⊥", 3, 1);
x_414 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_7);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_416 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_409, x_2, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_420 = lean_mk_string_unchecked("⊥ : ", 6, 4);
x_421 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_421, 0, x_420);
x_422 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_417);
x_423 = lean_mk_string_unchecked("", 0, 0);
x_424 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_424, 0, x_423);
x_425 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_424);
if (lean_is_scalar(x_419)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_419;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_418);
return x_426;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Compiler_LCNF_PP_ppParams(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Compiler_LCNF_PP_ppCode(x_10, x_2, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed), 1, 0);
x_19 = lean_mk_string_unchecked("| ", 2, 2);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Name_toString(x_8, x_22, x_18);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_tag(x_11, 5);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_20);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_13);
x_29 = lean_mk_string_unchecked(" =>", 3, 3);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_Format_indentD(x_17);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed), 1, 0);
x_38 = lean_mk_string_unchecked("| ", 2, 2);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(1);
x_41 = lean_unbox(x_40);
x_42 = l_Lean_Name_toString(x_8, x_41, x_37);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_tag(x_11, 5);
lean_ctor_set(x_11, 1, x_43);
lean_ctor_set(x_11, 0, x_39);
x_44 = lean_mk_string_unchecked("", 0, 0);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_inc(x_45);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_11);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_13);
x_48 = lean_mk_string_unchecked(" =>", 3, 3);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_Format_indentD(x_35);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_36);
return x_54;
}
}
else
{
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_8);
return x_15;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = l_Lean_Compiler_LCNF_PP_ppCode(x_10, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed), 1, 0);
x_62 = lean_mk_string_unchecked("| ", 2, 2);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_box(1);
x_65 = lean_unbox(x_64);
x_66 = l_Lean_Name_toString(x_8, x_65, x_61);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_inc(x_70);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_55);
x_73 = lean_mk_string_unchecked(" =>", 3, 3);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Std_Format_indentD(x_58);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
if (lean_is_scalar(x_60)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_60;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_59);
return x_79;
}
else
{
lean_dec(x_55);
lean_dec(x_8);
return x_57;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_1);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_1, 0);
x_82 = l_Lean_Compiler_LCNF_PP_ppCode(x_81, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_mk_string_unchecked("| _ =>", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_85);
x_86 = l_Std_Format_indentD(x_84);
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_mk_string_unchecked("", 0, 0);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_82, 0, x_90);
return x_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_82);
x_93 = lean_mk_string_unchecked("| _ =>", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_93);
x_94 = l_Std_Format_indentD(x_91);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("", 0, 0);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
return x_99;
}
}
else
{
lean_free_object(x_1);
return x_82;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
lean_dec(x_1);
x_101 = l_Lean_Compiler_LCNF_PP_ppCode(x_100, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_mk_string_unchecked("| _ =>", 6, 6);
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Std_Format_indentD(x_102);
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("", 0, 0);
x_110 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_104)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_104;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_103);
return x_112;
}
else
{
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_PP_ppFunDecl___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_PP_ppCode(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_mk_string_unchecked("extern", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("extern", 6, 6);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_76; uint8_t x_77; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = l_Lean_pp_sanitizeNames;
x_12 = lean_box(0);
x_13 = l_Lean_diagnostics;
x_14 = lean_unbox(x_12);
x_15 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_10, x_11, x_14);
x_16 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_15, x_13);
x_76 = lean_ctor_get(x_8, 0);
lean_inc(x_76);
lean_dec(x_8);
x_77 = l_Lean_Kernel_isDiagnosticsEnabled(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
if (x_16 == 0)
{
x_17 = x_4;
x_18 = x_5;
x_19 = x_9;
goto block_41;
}
else
{
goto block_75;
}
}
else
{
if (x_16 == 0)
{
goto block_75;
}
else
{
x_17 = x_4;
x_18 = x_5;
x_19 = x_9;
goto block_41;
}
}
block_41:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_20 = lean_st_ref_get(x_3, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_maxRecDepth;
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 3);
lean_inc(x_26);
x_27 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_15, x_23);
x_28 = lean_ctor_get(x_17, 5);
lean_inc(x_28);
x_29 = lean_ctor_get(x_17, 6);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 7);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 8);
lean_inc(x_31);
x_32 = lean_ctor_get(x_17, 9);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 10);
lean_inc(x_33);
x_34 = lean_ctor_get(x_17, 11);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_17, sizeof(void*)*13 + 1);
x_36 = lean_ctor_get(x_17, 12);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 3, x_26);
lean_ctor_set(x_37, 4, x_27);
lean_ctor_set(x_37, 5, x_28);
lean_ctor_set(x_37, 6, x_29);
lean_ctor_set(x_37, 7, x_30);
lean_ctor_set(x_37, 8, x_31);
lean_ctor_set(x_37, 9, x_32);
lean_ctor_set(x_37, 10, x_33);
lean_ctor_set(x_37, 11, x_34);
lean_ctor_set(x_37, 12, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_37, sizeof(void*)*13 + 1, x_35);
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
x_39 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_38);
lean_dec(x_38);
x_40 = lean_apply_6(x_1, x_39, x_2, x_3, x_37, x_18, x_22);
return x_40;
}
block_75:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_st_ref_take(x_5, x_9);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = l_Lean_Kernel_enableDiag(x_46, x_16);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_inc(x_52);
lean_ctor_set(x_42, 1, x_52);
lean_ctor_set(x_42, 0, x_52);
x_53 = lean_ctor_get(x_44, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_44, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 7);
lean_inc(x_55);
lean_dec(x_44);
x_56 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_42);
lean_ctor_set(x_56, 5, x_53);
lean_ctor_set(x_56, 6, x_54);
lean_ctor_set(x_56, 7, x_55);
x_57 = lean_st_ref_set(x_5, x_56, x_45);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_17 = x_4;
x_18 = x_5;
x_19 = x_58;
goto block_41;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_59 = lean_ctor_get(x_42, 0);
x_60 = lean_ctor_get(x_42, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_42);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = l_Lean_Kernel_enableDiag(x_61, x_16);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 3);
lean_inc(x_65);
x_66 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_ctor_get(x_59, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 6);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 7);
lean_inc(x_71);
lean_dec(x_59);
x_72 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_64);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_68);
lean_ctor_set(x_72, 5, x_69);
lean_ctor_set(x_72, 6, x_70);
lean_ctor_set(x_72, 7, x_71);
x_73 = lean_st_ref_set(x_5, x_72, x_60);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_17 = x_4;
x_18 = x_5;
x_19 = x_74;
goto block_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_PP_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_PP_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_LCNF_PP_ppParams(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_PP_getFunType(x_1, x_14, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_4);
x_18 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_16, x_4, x_7, x_8, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_2, 4);
lean_inc(x_22);
x_23 = l_Lean_Compiler_LCNF_PP_ppDeclValue(x_22, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_mk_string_unchecked("def ", 4, 4);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Name_toString(x_28, x_30, x_3);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_tag(x_18, 5);
lean_ctor_set(x_18, 1, x_32);
lean_ctor_set(x_18, 0, x_27);
x_33 = lean_mk_string_unchecked("", 0, 0);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_34);
lean_ctor_set_tag(x_10, 5);
lean_ctor_set(x_10, 1, x_34);
lean_ctor_set(x_10, 0, x_18);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_12);
x_36 = lean_mk_string_unchecked(" : ", 3, 3);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_20);
x_40 = lean_mk_string_unchecked(" :=", 3, 3);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Std_Format_indentD(x_25);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_23, 0, x_45);
return x_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_23);
x_48 = lean_mk_string_unchecked("def ", 4, 4);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
x_53 = l_Lean_Name_toString(x_50, x_52, x_3);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_tag(x_18, 5);
lean_ctor_set(x_18, 1, x_54);
lean_ctor_set(x_18, 0, x_49);
x_55 = lean_mk_string_unchecked("", 0, 0);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_inc(x_56);
lean_ctor_set_tag(x_10, 5);
lean_ctor_set(x_10, 1, x_56);
lean_ctor_set(x_10, 0, x_18);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_12);
x_58 = lean_mk_string_unchecked(" : ", 3, 3);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_20);
x_62 = lean_mk_string_unchecked(" :=", 3, 3);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Std_Format_indentD(x_46);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_56);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_47);
return x_68;
}
}
else
{
lean_free_object(x_18);
lean_dec(x_20);
lean_free_object(x_10);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
x_71 = lean_ctor_get(x_2, 4);
lean_inc(x_71);
x_72 = l_Lean_Compiler_LCNF_PP_ppDeclValue(x_71, x_4, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_mk_string_unchecked("def ", 4, 4);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
lean_dec(x_2);
x_79 = lean_box(1);
x_80 = lean_unbox(x_79);
x_81 = l_Lean_Name_toString(x_78, x_80, x_3);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("", 0, 0);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_inc(x_85);
lean_ctor_set_tag(x_10, 5);
lean_ctor_set(x_10, 1, x_85);
lean_ctor_set(x_10, 0, x_83);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_10);
lean_ctor_set(x_86, 1, x_12);
x_87 = lean_mk_string_unchecked(" : ", 3, 3);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_69);
x_91 = lean_mk_string_unchecked(" :=", 3, 3);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Std_Format_indentD(x_73);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_85);
if (lean_is_scalar(x_75)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_75;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_74);
return x_97;
}
else
{
lean_dec(x_69);
lean_free_object(x_10);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_72;
}
}
}
else
{
uint8_t x_98; 
lean_free_object(x_10);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_15);
if (x_98 == 0)
{
return x_15;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_15, 0);
x_100 = lean_ctor_get(x_15, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_15);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_10, 0);
x_103 = lean_ctor_get(x_10, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_10);
x_104 = lean_ctor_get(x_2, 2);
lean_inc(x_104);
x_105 = l_Lean_Compiler_LCNF_PP_getFunType(x_1, x_104, x_7, x_8, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_4);
x_108 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_106, x_4, x_7, x_8, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_2, 4);
lean_inc(x_112);
x_113 = l_Lean_Compiler_LCNF_PP_ppDeclValue(x_112, x_4, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_mk_string_unchecked("def ", 4, 4);
x_118 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_ctor_get(x_2, 0);
lean_inc(x_119);
lean_dec(x_2);
x_120 = lean_box(1);
x_121 = lean_unbox(x_120);
x_122 = l_Lean_Name_toString(x_119, x_121, x_3);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
if (lean_is_scalar(x_111)) {
 x_124 = lean_alloc_ctor(5, 2, 0);
} else {
 x_124 = x_111;
 lean_ctor_set_tag(x_124, 5);
}
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_mk_string_unchecked("", 0, 0);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_125);
lean_inc(x_126);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_102);
x_129 = lean_mk_string_unchecked(" : ", 3, 3);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_109);
x_133 = lean_mk_string_unchecked(" :=", 3, 3);
x_134 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Std_Format_indentD(x_114);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_126);
if (lean_is_scalar(x_116)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_116;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_115);
return x_139;
}
else
{
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_102);
lean_dec(x_3);
lean_dec(x_2);
return x_113;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_102);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = lean_ctor_get(x_105, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_105, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_142 = x_105;
} else {
 lean_dec_ref(x_105);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppFVar___redArg___lam__0___boxed), 1, 0);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__1), 9, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_7);
x_10 = l_Lean_Compiler_LCNF_PP_run___redArg(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_mk_string_unchecked("fun ", 4, 4);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_mk_string_unchecked("fun ", 4, 4);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_mk_string_unchecked("", 0, 0);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
}
else
{
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_PP_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_set(x_1, x_2, x_4);
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
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(8u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_shiftl(x_9, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_div(x_12, x_13);
lean_dec(x_12);
x_15 = l_Nat_nextPowerOfTwo(x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_mk_array(x_15, x_16);
lean_ctor_set(x_5, 1, x_17);
lean_ctor_set(x_5, 0, x_10);
lean_inc_n(x_5, 2);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
lean_inc(x_3);
x_23 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_1, x_20, x_22, x_2, x_3, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_3, x_7, x_26, x_25);
lean_dec(x_26);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_box(0);
x_35 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_3, x_7, x_34, x_33);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_unsigned_to_nat(8u);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_shiftl(x_42, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = l_Nat_nextPowerOfTwo(x_47);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = lean_mk_array(x_48, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
lean_inc_n(x_51, 2);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(0);
x_56 = lean_unbox(x_55);
lean_inc(x_3);
x_57 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_1, x_54, x_56, x_2, x_3, x_41);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_3, x_40, x_60, x_59);
lean_dec(x_60);
lean_dec(x_3);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_box(0);
x_68 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_3, x_40, x_67, x_66);
lean_dec(x_3);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_ppDecl(x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0), 7, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(x_15, x_2, x_3, x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Compiler_LCNF_Code_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_ppCode(x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0), 7, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(x_15, x_2, x_3, x_4);
return x_16;
}
}
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
