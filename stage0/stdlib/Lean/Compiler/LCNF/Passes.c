// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.CSE Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.PullFunDecls Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.JoinPoints Lean.Compiler.LCNF.Specialize Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.ToMono Lean.Compiler.LCNF.LambdaLifting Lean.Compiler.LCNF.FloatLetIn Lean.Compiler.LCNF.ReduceArity Lean.Compiler.LCNF.ElimDeadBranches
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
lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_851_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_851____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__3____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_ImportM_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_lambdaLifting;
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_999_(lean_object*);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_851_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_reduceArity;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_eagerLambdaLifting;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_findJoinPoints;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_pullInstances;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace(uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_elimDeadBranches;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_passManagerExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_toMono;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_pullFunDecls;
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_492____boxed(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_851_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
uint8_t l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_162_(uint8_t, uint8_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_builtinPassManager;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_851____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___boxed(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_specialize;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_8, x_5, x_6);
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
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_8, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_box(0);
x_14 = lean_usize_of_nat(x_1);
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(x_2, x_14, x_15, x_13, x_6, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_init() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_init___lam__0___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("init", 4, 4);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_8);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_init_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_init___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_init___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_trace___lam__0___boxed), 6, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_string_unchecked("trace", 5, 5);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_trace___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trace___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_LCNF_trace(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_8, x_5, x_9);
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveBase() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveBase___lam__0___boxed), 6, 0);
x_2 = lean_mk_string_unchecked("saveBase", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_3, x_1, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBase___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_saveBase___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_8, x_5, x_9);
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_saveMono() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveMono___lam__0___boxed), 6, 0);
x_2 = lean_mk_string_unchecked("saveMono", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unbox(x_4);
x_7 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_3, x_1, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMono___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_saveMono___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtinPassManager() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_1 = l_Lean_Compiler_LCNF_init;
x_2 = l_Lean_Compiler_LCNF_pullInstances;
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unbox(x_3);
x_7 = lean_unbox(x_4);
x_8 = l_Lean_Compiler_LCNF_cse(x_6, x_7, x_5);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 0, 4);
x_11 = lean_unbox(x_4);
lean_ctor_set_uint8(x_10, 0, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_10, 1, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_10, 2, x_13);
x_14 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, 3, x_14);
x_15 = lean_unbox(x_3);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_simp(x_10, x_5, x_15);
x_17 = lean_unbox(x_3);
x_18 = l_Lean_Compiler_LCNF_floatLetIn(x_17, x_5);
x_19 = l_Lean_Compiler_LCNF_findJoinPoints;
x_20 = l_Lean_Compiler_LCNF_pullFunDecls;
x_21 = lean_unbox(x_3);
x_22 = l_Lean_Compiler_LCNF_reduceJpArity(x_21);
x_23 = lean_alloc_ctor(0, 0, 4);
x_24 = lean_unbox(x_9);
lean_ctor_set_uint8(x_23, 0, x_24);
x_25 = lean_unbox(x_9);
lean_ctor_set_uint8(x_23, 1, x_25);
x_26 = lean_unbox(x_9);
lean_ctor_set_uint8(x_23, 2, x_26);
x_27 = lean_unbox(x_9);
lean_ctor_set_uint8(x_23, 3, x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_unbox(x_3);
x_30 = l_Lean_Compiler_LCNF_simp(x_23, x_28, x_29);
x_31 = l_Lean_Compiler_LCNF_eagerLambdaLifting;
x_32 = l_Lean_Compiler_LCNF_specialize;
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_unbox(x_3);
lean_inc(x_10);
x_35 = l_Lean_Compiler_LCNF_simp(x_10, x_33, x_34);
x_36 = lean_unbox(x_3);
x_37 = lean_unbox(x_4);
x_38 = l_Lean_Compiler_LCNF_cse(x_36, x_37, x_28);
x_39 = l_Lean_Compiler_LCNF_saveBase;
x_40 = l_Lean_Compiler_LCNF_toMono;
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_box(1);
x_43 = lean_unbox(x_42);
lean_inc(x_10);
x_44 = l_Lean_Compiler_LCNF_simp(x_10, x_41, x_43);
x_45 = lean_unbox(x_42);
x_46 = l_Lean_Compiler_LCNF_reduceJpArity(x_45);
x_47 = lean_unbox(x_42);
x_48 = l_Lean_Compiler_LCNF_extendJoinPointContext(x_5, x_47, lean_box(0));
x_49 = lean_unbox(x_42);
x_50 = l_Lean_Compiler_LCNF_floatLetIn(x_49, x_28);
x_51 = l_Lean_Compiler_LCNF_reduceArity;
x_52 = l_Lean_Compiler_LCNF_commonJoinPointArgs;
x_53 = lean_unsigned_to_nat(4u);
x_54 = lean_unbox(x_42);
lean_inc(x_10);
x_55 = l_Lean_Compiler_LCNF_simp(x_10, x_53, x_54);
x_56 = lean_unbox(x_42);
x_57 = l_Lean_Compiler_LCNF_floatLetIn(x_56, x_33);
x_58 = l_Lean_Compiler_LCNF_elimDeadBranches;
x_59 = l_Lean_Compiler_LCNF_lambdaLifting;
x_60 = lean_unbox(x_42);
x_61 = l_Lean_Compiler_LCNF_extendJoinPointContext(x_28, x_60, lean_box(0));
x_62 = lean_unsigned_to_nat(5u);
x_63 = lean_unbox(x_42);
x_64 = l_Lean_Compiler_LCNF_simp(x_10, x_62, x_63);
x_65 = lean_unbox(x_42);
x_66 = lean_unbox(x_4);
x_67 = l_Lean_Compiler_LCNF_cse(x_65, x_66, x_33);
x_68 = l_Lean_Compiler_LCNF_saveMono;
x_69 = lean_unsigned_to_nat(29u);
x_70 = lean_mk_empty_array_with_capacity(x_69);
x_71 = lean_array_push(x_70, x_1);
x_72 = lean_array_push(x_71, x_2);
x_73 = lean_array_push(x_72, x_8);
x_74 = lean_array_push(x_73, x_16);
x_75 = lean_array_push(x_74, x_18);
x_76 = lean_array_push(x_75, x_19);
x_77 = lean_array_push(x_76, x_20);
x_78 = lean_array_push(x_77, x_22);
x_79 = lean_array_push(x_78, x_30);
x_80 = lean_array_push(x_79, x_31);
x_81 = lean_array_push(x_80, x_32);
x_82 = lean_array_push(x_81, x_35);
x_83 = lean_array_push(x_82, x_38);
x_84 = lean_array_push(x_83, x_39);
x_85 = lean_array_push(x_84, x_40);
x_86 = lean_array_push(x_85, x_44);
x_87 = lean_array_push(x_86, x_46);
x_88 = lean_array_push(x_87, x_48);
x_89 = lean_array_push(x_88, x_50);
x_90 = lean_array_push(x_89, x_51);
x_91 = lean_array_push(x_90, x_52);
x_92 = lean_array_push(x_91, x_55);
x_93 = lean_array_push(x_92, x_57);
x_94 = lean_array_push(x_93, x_58);
x_95 = lean_array_push(x_94, x_59);
x_96 = lean_array_push(x_95, x_61);
x_97 = lean_array_push(x_96, x_64);
x_98 = lean_array_push(x_97, x_67);
x_99 = lean_array_push(x_98, x_68);
return x_99;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_1, x_3);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(x_4, x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_12;
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_array_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(x_10, x_11, x_13, x_4, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_15;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; lean_object* x_9; 
x_5 = l_Lean_Compiler_LCNF_builtinPassManager;
x_6 = lean_array_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(x_1, x_6, x_8, x_5, x_2, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_runImportedDecls_spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runImportedDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_runImportedDecls(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_List_reverse___redArg(x_2);
x_4 = lean_array_mk(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_7);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_14 = x_2;
} else {
 lean_dec_ref(x_2);
 x_14 = lean_box(0);
}
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_11);
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__3____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_runImportedDecls___boxed), 4, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_ImportM_runCoreM___redArg(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_492____boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_492_), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__2____x40_Lean_Compiler_LCNF_Passes___hyg_492_), 2, 0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Compiler", 8, 8);
x_7 = lean_mk_string_unchecked("LCNF", 4, 4);
x_8 = lean_mk_string_unchecked("passManagerExt", 14, 14);
x_9 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__3____x40_Lean_Compiler_LCNF_Passes___hyg_492_), 4, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_Lean_Compiler_LCNF_builtinPassManager;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__4____x40_Lean_Compiler_LCNF_Passes___hyg_492_), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_box(2);
x_16 = lean_box(0);
lean_inc(x_3);
x_17 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_4);
lean_ctor_set(x_17, 4, x_3);
lean_ctor_set(x_17, 5, x_3);
lean_ctor_set(x_17, 6, x_2);
lean_ctor_set(x_17, 7, x_16);
x_18 = lean_unbox(x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*8, x_18);
x_19 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(x_17, x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_492____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_492_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_instInhabitedList(lean_box(0));
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Lean_Compiler_LCNF_passManagerExt;
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec(x_11);
x_13 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_8, x_10, x_9, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = l_instInhabitedList(lean_box(0));
x_18 = l_Array_empty(lean_box(0));
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_Compiler_LCNF_passManagerExt;
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
lean_dec(x_22);
x_24 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_19, x_21, x_20, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_getPassManager___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_getPassManager___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getPassManager___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_getPassManager(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_mk_string_unchecked("invalid 'cpass' only 'PassInstaller's can be added via the 'cpass' attribute: ", 78, 78);
x_7 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_8 = l_Lean_ConstantInfo_type(x_1);
x_9 = l_Lean_MessageData_ofExpr(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_13, x_3, x_4, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_ConstantInfo_type(x_6);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Expr_bvar___override(x_9);
x_11 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_10, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_10);
lean_dec(x_6);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Expr_fvar___override(x_12);
x_14 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_13, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_13);
lean_dec(x_6);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_Expr_mvar___override(x_15);
x_17 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_16, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_16);
lean_dec(x_6);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = l_Lean_Expr_sort___override(x_18);
x_20 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_19, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_19);
lean_dec(x_6);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_box(0);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = l_Lean_Expr_const___override(x_23, x_22);
x_25 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_24, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_24);
lean_dec(x_6);
return x_25;
}
case 1:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_Name_str___override(x_23, x_27);
x_29 = l_Lean_Expr_const___override(x_28, x_22);
x_30 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_29, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_29);
lean_dec(x_6);
return x_30;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
lean_inc(x_33);
x_34 = l_Lean_Name_str___override(x_23, x_33);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_1);
x_35 = l_Lean_Name_str___override(x_34, x_31);
x_36 = l_Lean_Expr_const___override(x_35, x_22);
x_37 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_36, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_36);
lean_dec(x_6);
return x_37;
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
lean_inc(x_39);
x_40 = l_Lean_Name_str___override(x_23, x_39);
lean_inc(x_33);
x_41 = l_Lean_Name_str___override(x_40, x_33);
switch (lean_obj_tag(x_38)) {
case 0:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_33);
lean_dec(x_1);
x_42 = l_Lean_Name_str___override(x_41, x_31);
x_43 = l_Lean_Expr_const___override(x_42, x_22);
x_44 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_43, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_43);
lean_dec(x_6);
return x_44;
}
case 1:
{
lean_object* x_45; 
lean_dec(x_41);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
switch (lean_obj_tag(x_45)) {
case 0:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_mk_string_unchecked("Lean", 4, 4);
x_48 = lean_string_dec_eq(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_1);
x_49 = l_Lean_Name_str___override(x_23, x_46);
x_50 = l_Lean_Name_str___override(x_49, x_39);
x_51 = l_Lean_Name_str___override(x_50, x_33);
x_52 = l_Lean_Name_str___override(x_51, x_31);
x_53 = l_Lean_Expr_const___override(x_52, x_22);
x_54 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_53, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_53);
lean_dec(x_6);
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_46);
x_55 = lean_mk_string_unchecked("Compiler", 8, 8);
x_56 = lean_string_dec_eq(x_39, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_dec(x_1);
x_57 = l_Lean_Name_str___override(x_23, x_47);
x_58 = l_Lean_Name_str___override(x_57, x_39);
x_59 = l_Lean_Name_str___override(x_58, x_33);
x_60 = l_Lean_Name_str___override(x_59, x_31);
x_61 = l_Lean_Expr_const___override(x_60, x_22);
x_62 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_61, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_61);
lean_dec(x_6);
return x_62;
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_39);
x_63 = lean_mk_string_unchecked("LCNF", 4, 4);
x_64 = lean_string_dec_eq(x_33, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
lean_dec(x_1);
x_65 = l_Lean_Name_str___override(x_23, x_47);
x_66 = l_Lean_Name_str___override(x_65, x_55);
x_67 = l_Lean_Name_str___override(x_66, x_33);
x_68 = l_Lean_Name_str___override(x_67, x_31);
x_69 = l_Lean_Expr_const___override(x_68, x_22);
x_70 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_69, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_69);
lean_dec(x_6);
return x_70;
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_dec(x_33);
x_71 = lean_mk_string_unchecked("PassInstaller", 13, 13);
x_72 = lean_string_dec_eq(x_31, x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_73 = l_Lean_Name_str___override(x_23, x_47);
x_74 = l_Lean_Name_str___override(x_73, x_55);
x_75 = l_Lean_Name_str___override(x_74, x_63);
x_76 = l_Lean_Name_str___override(x_75, x_31);
x_77 = l_Lean_Expr_const___override(x_76, x_22);
x_78 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_77, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_77);
lean_dec(x_6);
return x_78;
}
else
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_63);
lean_dec(x_55);
lean_dec(x_47);
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_6);
x_79 = l_Lean_Compiler_LCNF_getPassManager___redArg(x_3, x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_3);
lean_inc(x_1);
x_83 = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(x_81, x_1, x_2, x_3, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_take(x_3, x_85);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = l_Lean_Compiler_LCNF_passManagerExt;
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 0, x_1);
x_92 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_91, x_90, x_86);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 3);
lean_inc(x_95);
x_96 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_inc(x_97);
lean_ctor_set(x_79, 1, x_97);
lean_ctor_set(x_79, 0, x_97);
x_98 = lean_ctor_get(x_88, 5);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 7);
lean_inc(x_100);
lean_dec(x_88);
x_101 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_94);
lean_ctor_set(x_101, 3, x_95);
lean_ctor_set(x_101, 4, x_79);
lean_ctor_set(x_101, 5, x_98);
lean_ctor_set(x_101, 6, x_99);
lean_ctor_set(x_101, 7, x_100);
x_102 = lean_st_ref_set(x_3, x_101, x_89);
lean_dec(x_3);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
x_105 = lean_box(0);
lean_ctor_set(x_102, 0, x_105);
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_109 = lean_ctor_get(x_86, 0);
x_110 = lean_ctor_get(x_86, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_86);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = l_Lean_Compiler_LCNF_passManagerExt;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_84);
x_114 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_112, x_111, x_113);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_109, 3);
lean_inc(x_117);
x_118 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_inc(x_119);
lean_ctor_set(x_79, 1, x_119);
lean_ctor_set(x_79, 0, x_119);
x_120 = lean_ctor_get(x_109, 5);
lean_inc(x_120);
x_121 = lean_ctor_get(x_109, 6);
lean_inc(x_121);
x_122 = lean_ctor_get(x_109, 7);
lean_inc(x_122);
lean_dec(x_109);
x_123 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_123, 0, x_114);
lean_ctor_set(x_123, 1, x_115);
lean_ctor_set(x_123, 2, x_116);
lean_ctor_set(x_123, 3, x_117);
lean_ctor_set(x_123, 4, x_79);
lean_ctor_set(x_123, 5, x_120);
lean_ctor_set(x_123, 6, x_121);
lean_ctor_set(x_123, 7, x_122);
x_124 = lean_st_ref_set(x_3, x_123, x_110);
lean_dec(x_3);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_free_object(x_79);
lean_dec(x_3);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_83);
if (x_129 == 0)
{
return x_83;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_83, 0);
x_131 = lean_ctor_get(x_83, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_83);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_79, 0);
x_134 = lean_ctor_get(x_79, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_79);
lean_inc(x_3);
lean_inc(x_1);
x_135 = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(x_133, x_1, x_2, x_3, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_st_ref_take(x_3, x_137);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = l_Lean_Compiler_LCNF_passManagerExt;
if (lean_is_scalar(x_141)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_141;
}
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_136);
x_145 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_143, x_142, x_144);
x_146 = lean_ctor_get(x_139, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_139, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_139, 3);
lean_inc(x_148);
x_149 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
lean_inc(x_150);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_ctor_get(x_139, 5);
lean_inc(x_152);
x_153 = lean_ctor_get(x_139, 6);
lean_inc(x_153);
x_154 = lean_ctor_get(x_139, 7);
lean_inc(x_154);
lean_dec(x_139);
x_155 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_155, 0, x_145);
lean_ctor_set(x_155, 1, x_146);
lean_ctor_set(x_155, 2, x_147);
lean_ctor_set(x_155, 3, x_148);
lean_ctor_set(x_155, 4, x_151);
lean_ctor_set(x_155, 5, x_152);
lean_ctor_set(x_155, 6, x_153);
lean_ctor_set(x_155, 7, x_154);
x_156 = lean_st_ref_set(x_3, x_155, x_140);
lean_dec(x_3);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_ctor_get(x_135, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_135, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_163 = x_135;
} else {
 lean_dec_ref(x_135);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_1);
x_165 = lean_ctor_get(x_38, 1);
lean_inc(x_165);
lean_dec(x_38);
x_166 = lean_ctor_get(x_45, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_45, 1);
lean_inc(x_167);
lean_dec(x_45);
x_168 = l_Lean_Name_str___override(x_166, x_167);
x_169 = l_Lean_Name_str___override(x_168, x_165);
x_170 = l_Lean_Name_str___override(x_169, x_39);
x_171 = l_Lean_Name_str___override(x_170, x_33);
x_172 = l_Lean_Name_str___override(x_171, x_31);
x_173 = l_Lean_Expr_const___override(x_172, x_22);
x_174 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_173, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_173);
lean_dec(x_6);
return x_174;
}
default: 
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_1);
x_175 = lean_ctor_get(x_38, 1);
lean_inc(x_175);
lean_dec(x_38);
x_176 = lean_ctor_get(x_45, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_45, 1);
lean_inc(x_177);
lean_dec(x_45);
x_178 = l_Lean_Name_num___override(x_176, x_177);
x_179 = l_Lean_Name_str___override(x_178, x_175);
x_180 = l_Lean_Name_str___override(x_179, x_39);
x_181 = l_Lean_Name_str___override(x_180, x_33);
x_182 = l_Lean_Name_str___override(x_181, x_31);
x_183 = l_Lean_Expr_const___override(x_182, x_22);
x_184 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_183, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_183);
lean_dec(x_6);
return x_184;
}
}
}
default: 
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_41);
lean_dec(x_1);
x_185 = lean_ctor_get(x_38, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_38, 1);
lean_inc(x_186);
lean_dec(x_38);
x_187 = l_Lean_Name_num___override(x_185, x_186);
x_188 = l_Lean_Name_str___override(x_187, x_39);
x_189 = l_Lean_Name_str___override(x_188, x_33);
x_190 = l_Lean_Name_str___override(x_189, x_31);
x_191 = l_Lean_Expr_const___override(x_190, x_22);
x_192 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_191, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_191);
lean_dec(x_6);
return x_192;
}
}
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_34);
lean_dec(x_1);
x_193 = lean_ctor_get(x_32, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_32, 1);
lean_inc(x_194);
lean_dec(x_32);
x_195 = l_Lean_Name_num___override(x_193, x_194);
x_196 = l_Lean_Name_str___override(x_195, x_33);
x_197 = l_Lean_Name_str___override(x_196, x_31);
x_198 = l_Lean_Expr_const___override(x_197, x_22);
x_199 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_198, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_198);
lean_dec(x_6);
return x_199;
}
}
}
default: 
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_1);
x_200 = lean_ctor_get(x_21, 1);
lean_inc(x_200);
lean_dec(x_21);
x_201 = lean_ctor_get(x_26, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_26, 1);
lean_inc(x_202);
lean_dec(x_26);
x_203 = l_Lean_Name_num___override(x_201, x_202);
x_204 = l_Lean_Name_str___override(x_203, x_200);
x_205 = l_Lean_Expr_const___override(x_204, x_22);
x_206 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_205, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_205);
lean_dec(x_6);
return x_206;
}
}
}
default: 
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_1);
x_207 = lean_ctor_get(x_21, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_21, 1);
lean_inc(x_208);
lean_dec(x_21);
x_209 = l_Lean_Name_num___override(x_207, x_208);
x_210 = l_Lean_Expr_const___override(x_209, x_22);
x_211 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_210, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_210);
lean_dec(x_6);
return x_211;
}
}
}
case 5:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_1);
x_212 = lean_ctor_get(x_8, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_8, 1);
lean_inc(x_213);
lean_dec(x_8);
x_214 = l_Lean_Expr_app___override(x_212, x_213);
x_215 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_214, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_214);
lean_dec(x_6);
return x_215;
}
case 6:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_1);
x_216 = lean_ctor_get(x_8, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_8, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_8, 2);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_220 = l_Lean_Expr_lam___override(x_216, x_217, x_218, x_219);
x_221 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_220, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_220);
lean_dec(x_6);
return x_221;
}
case 7:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_1);
x_222 = lean_ctor_get(x_8, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_8, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_8, 2);
lean_inc(x_224);
x_225 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 8);
lean_dec(x_8);
x_226 = l_Lean_Expr_forallE___override(x_222, x_223, x_224, x_225);
x_227 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_226, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_226);
lean_dec(x_6);
return x_227;
}
case 8:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_1);
x_228 = lean_ctor_get(x_8, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_8, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_8, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_8, 3);
lean_inc(x_231);
x_232 = lean_ctor_get_uint8(x_8, sizeof(void*)*4 + 8);
lean_dec(x_8);
x_233 = l_Lean_Expr_letE___override(x_228, x_229, x_230, x_231, x_232);
x_234 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_233, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_233);
lean_dec(x_6);
return x_234;
}
case 9:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_1);
x_235 = lean_ctor_get(x_8, 0);
lean_inc(x_235);
lean_dec(x_8);
x_236 = l_Lean_Expr_lit___override(x_235);
x_237 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_236, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_236);
lean_dec(x_6);
return x_237;
}
case 10:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_1);
x_238 = lean_ctor_get(x_8, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_8, 1);
lean_inc(x_239);
lean_dec(x_8);
x_240 = l_Lean_Expr_mdata___override(x_238, x_239);
x_241 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_240, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_240);
lean_dec(x_6);
return x_241;
}
default: 
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_1);
x_242 = lean_ctor_get(x_8, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_8, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_8, 2);
lean_inc(x_244);
lean_dec(x_8);
x_245 = l_Lean_Expr_proj___override(x_242, x_243, x_244);
x_246 = l_Lean_Compiler_LCNF_addPass___lam__0(x_6, x_245, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_245);
lean_dec(x_6);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_5);
if (x_247 == 0)
{
return x_5;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_5, 0);
x_249 = lean_ctor_get(x_5, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_5);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_addPass___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_addPass___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_851_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_851_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Attribute_Builtin_ensureNoArgs(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_162_(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("invalid attribute 'cpass', must be global", 41, 41);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_13, x_4, x_5, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_addPass(x_1, x_4, x_5, x_8);
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
return x_15;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_851_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_851____boxed), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_851____boxed), 6, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Compiler", 8, 8);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("LCNF", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_5);
x_16 = l_Lean_Name_str___override(x_15, x_7);
x_17 = l_Lean_Name_str___override(x_16, x_9);
x_18 = lean_mk_string_unchecked("Passes", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(851u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("cpass", 5, 5);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_mk_string_unchecked("compiler passes for the code generator", 38, 38);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_29);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_2);
x_31 = l_Lean_registerBuiltinAttribute(x_30, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_851____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_initFn___lam__0____x40_Lean_Compiler_LCNF_Passes___hyg_851_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_851____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Compiler_LCNF_initFn___lam__1____x40_Lean_Compiler_LCNF_Passes___hyg_851_(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_999_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("saveBase", 8, 8);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("LCNF", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
lean_inc(x_2);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("Passes", 6, 6);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(999u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
lean_inc(x_24);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("saveMono", 8, 8);
lean_inc(x_2);
x_29 = l_Lean_Name_mkStr2(x_2, x_28);
x_30 = lean_unbox(x_5);
lean_inc(x_24);
x_31 = l_Lean_registerTraceClass(x_29, x_30, x_24, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("trace", 5, 5);
x_34 = l_Lean_Name_mkStr2(x_2, x_33);
x_35 = lean_unbox(x_5);
x_36 = l_Lean_registerTraceClass(x_34, x_35, x_24, x_32);
return x_36;
}
else
{
lean_dec(x_24);
lean_dec(x_2);
return x_31;
}
}
else
{
lean_dec(x_24);
lean_dec(x_2);
return x_26;
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToMono(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_LambdaLifting(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ElimDeadBranches(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CSE(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullFunDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_JoinPoints(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Specialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToMono(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_LambdaLifting(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FloatLetIn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceArity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_init = _init_l_Lean_Compiler_LCNF_init();
lean_mark_persistent(l_Lean_Compiler_LCNF_init);
l_Lean_Compiler_LCNF_saveBase = _init_l_Lean_Compiler_LCNF_saveBase();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveBase);
l_Lean_Compiler_LCNF_saveMono = _init_l_Lean_Compiler_LCNF_saveMono();
lean_mark_persistent(l_Lean_Compiler_LCNF_saveMono);
l_Lean_Compiler_LCNF_builtinPassManager = _init_l_Lean_Compiler_LCNF_builtinPassManager();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_492_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_passManagerExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_passManagerExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_851_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Passes___hyg_999_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
