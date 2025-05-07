// Lean compiler output
// Module: Lean.Compiler.InitAttr
// Imports: Lean.AddDecl Lean.MonadEnv Lean.Elab.InfoTree.Main
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
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInitializerExecutionEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_1174_(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setBuiltinInitAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Compiler_InitAttr___hyg_1133_;
LEAN_EXPORT lean_object* l_Lean_getInitFnNameForCore_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_interpretedModInits;
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_runInit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_regular_init_fn_name_for(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lean_builtinInitAttr;
LEAN_EXPORT lean_object* l_Lean_isIOUnitInitFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getInitFnNameForCore_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_run_mod_init(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_218_(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___boxed(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIOUnitRegularInitFn___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_io_unit_regular_init_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_io_unit_builtin_init_fn(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* lean_run_init(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIOUnitInitFnCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIOUnitInitFnCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_builtin_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_runModInit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_regularInitAttr;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasInitAttr___boxed(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_1146_(lean_object*);
lean_object* l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___boxed(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit___boxed(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIOUnitInitFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_isIOUnitBuiltinInitFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_mk_string_unchecked("IO", 2, 2);
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
return x_5;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
return x_5;
}
}
}
else
{
return x_5;
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_mk_string_unchecked("Unit", 4, 4);
x_7 = lean_string_dec_eq(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_unbox(x_3);
return x_9;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
return x_7;
}
else
{
uint8_t x_10; 
x_10 = lean_unbox(x_3);
return x_10;
}
}
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_3);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_Compiler_InitAttr_0__Lean_isUnitType(x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_runModInit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_run_mod_init(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_runInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_run_init(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_218_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_shiftr(x_5, x_6);
lean_dec(x_5);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___lam__0(x_8, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___lam__0(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_15 = lean_nat_dec_lt(x_14, x_3);
if (x_15 == 0)
{
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_box(0);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_3);
x_19 = lean_nat_add(x_7, x_6);
lean_dec(x_7);
x_20 = lean_nat_dec_le(x_19, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_4);
x_21 = lean_box(0);
return x_21;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
x_9 = x_18;
x_10 = x_8;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_20, x_22);
lean_dec(x_20);
x_24 = lean_nat_dec_le(x_19, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
x_9 = x_18;
x_10 = x_8;
goto block_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_array_uget(x_4, x_6);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg(x_1, x_27, x_19, x_23);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
x_9 = x_18;
x_10 = x_8;
goto block_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Name_isAnonymous(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_run_init(x_3, x_33, x_30, x_31, x_8);
lean_dec(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_9 = x_18;
x_10 = x_35;
goto block_15;
}
else
{
return x_34;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_eval_const(x_3, x_36, x_30);
lean_dec(x_30);
x_38 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_37, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_apply_1(x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_9 = x_18;
x_10 = x_42;
goto block_15;
}
else
{
return x_41;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_6, x_12);
x_6 = x_13;
x_7 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_1);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
x_10 = x_19;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_21, x_23);
lean_dec(x_21);
x_25 = lean_nat_dec_le(x_20, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
x_10 = x_19;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_array_uget(x_4, x_6);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg(x_1, x_28, x_20, x_24);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
x_10 = x_19;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Name_isAnonymous(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_run_init(x_3, x_34, x_31, x_32, x_9);
lean_dec(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_10 = x_19;
x_11 = x_36;
goto block_16;
}
else
{
return x_35;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_eval_const(x_3, x_37, x_31);
lean_dec(x_31);
x_39 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_38, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_apply_1(x_40, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_10 = x_19;
x_11 = x_43;
goto block_16;
}
else
{
return x_42;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_6, x_13);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_14, x_10, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_20, x_26);
lean_inc(x_25);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_21);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_array_uget(x_3, x_5);
lean_inc(x_34);
x_35 = lean_run_mod_init(x_34, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_nat_add(x_29, x_26);
lean_inc(x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_30);
x_41 = lean_unbox(x_36);
lean_dec(x_36);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_array_fget(x_25, x_20);
lean_dec(x_20);
lean_dec(x_25);
x_43 = l_Array_isEmpty___redArg(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_interpretedModInits;
x_45 = lean_st_ref_get(x_44, x_37);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = l_Lean_NameSet_contains(x_47, x_34);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_free_object(x_45);
x_50 = lean_st_ref_take(x_44, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_NameSet_insert(x_51, x_34);
x_54 = lean_st_ref_set(x_44, x_53, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; size_t x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_54, 1);
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_array_fget(x_38, x_29);
lean_dec(x_29);
lean_dec(x_38);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = lean_array_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_usize_of_nat(x_62);
x_64 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(x_42, x_1, x_2, x_59, x_61, x_63, x_60, x_7, x_56);
lean_dec(x_59);
lean_dec(x_42);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_ctor_set(x_54, 1, x_28);
lean_ctor_set(x_54, 0, x_40);
x_9 = x_54;
x_10 = x_65;
goto block_15;
}
else
{
uint8_t x_66; 
lean_free_object(x_54);
lean_dec(x_40);
lean_dec(x_28);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_64);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_54, 1);
lean_inc(x_70);
lean_dec(x_54);
x_71 = lean_array_fget(x_38, x_29);
lean_dec(x_29);
lean_dec(x_38);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = lean_array_size(x_72);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_usize_of_nat(x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(x_42, x_1, x_2, x_72, x_74, x_76, x_73, x_7, x_70);
lean_dec(x_72);
lean_dec(x_42);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_40);
lean_ctor_set(x_79, 1, x_28);
x_9 = x_79;
x_10 = x_78;
goto block_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_40);
lean_dec(x_28);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_82 = x_77;
} else {
 lean_dec_ref(x_77);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 0, x_40);
x_9 = x_45;
x_10 = x_48;
goto block_15;
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_45, 0);
x_85 = lean_ctor_get(x_45, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_45);
x_86 = l_Lean_NameSet_contains(x_84, x_34);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; lean_object* x_98; size_t x_99; lean_object* x_100; 
x_87 = lean_st_ref_take(x_44, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_NameSet_insert(x_88, x_34);
x_91 = lean_st_ref_set(x_44, x_90, x_89);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_array_fget(x_38, x_29);
lean_dec(x_29);
lean_dec(x_38);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_box(0);
x_97 = lean_array_size(x_95);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_usize_of_nat(x_98);
x_100 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(x_42, x_1, x_2, x_95, x_97, x_99, x_96, x_7, x_92);
lean_dec(x_95);
lean_dec(x_42);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
if (lean_is_scalar(x_93)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_93;
}
lean_ctor_set(x_102, 0, x_40);
lean_ctor_set(x_102, 1, x_28);
x_9 = x_102;
x_10 = x_101;
goto block_15;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_93);
lean_dec(x_40);
lean_dec(x_28);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_105 = x_100;
} else {
 lean_dec_ref(x_100);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_40);
lean_ctor_set(x_107, 1, x_28);
x_9 = x_107;
x_10 = x_85;
goto block_15;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_40);
lean_ctor_set(x_108, 1, x_28);
x_9 = x_108;
x_10 = x_37;
goto block_15;
}
}
else
{
lean_object* x_109; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_40);
lean_ctor_set(x_109, 1, x_28);
x_9 = x_109;
x_10 = x_37;
goto block_15;
}
}
else
{
uint8_t x_110; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
x_110 = !lean_is_exclusive(x_35);
if (x_110 == 0)
{
return x_35;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_35, 0);
x_112 = lean_ctor_get(x_35, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_35);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_20, x_26);
lean_inc(x_25);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_21);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_array_uget(x_3, x_5);
lean_inc(x_34);
x_35 = lean_run_mod_init(x_34, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_nat_add(x_29, x_26);
lean_inc(x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_30);
x_41 = lean_unbox(x_36);
lean_dec(x_36);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_array_fget(x_25, x_20);
lean_dec(x_20);
lean_dec(x_25);
x_43 = l_Array_isEmpty___redArg(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_interpretedModInits;
x_45 = lean_st_ref_get(x_44, x_37);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = l_Lean_NameSet_contains(x_47, x_34);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_free_object(x_45);
x_50 = lean_st_ref_take(x_44, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_NameSet_insert(x_51, x_34);
x_54 = lean_st_ref_set(x_44, x_53, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; size_t x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_54, 1);
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_array_fget(x_38, x_29);
lean_dec(x_29);
lean_dec(x_38);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = lean_array_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_usize_of_nat(x_62);
x_64 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(x_42, x_1, x_2, x_59, x_61, x_63, x_60, x_7, x_56);
lean_dec(x_59);
lean_dec(x_42);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_ctor_set(x_54, 1, x_28);
lean_ctor_set(x_54, 0, x_40);
x_9 = x_54;
x_10 = x_65;
goto block_15;
}
else
{
uint8_t x_66; 
lean_free_object(x_54);
lean_dec(x_40);
lean_dec(x_28);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_64);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_54, 1);
lean_inc(x_70);
lean_dec(x_54);
x_71 = lean_array_fget(x_38, x_29);
lean_dec(x_29);
lean_dec(x_38);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = lean_array_size(x_72);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_usize_of_nat(x_75);
x_77 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(x_42, x_1, x_2, x_72, x_74, x_76, x_73, x_7, x_70);
lean_dec(x_72);
lean_dec(x_42);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_40);
lean_ctor_set(x_79, 1, x_28);
x_9 = x_79;
x_10 = x_78;
goto block_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_40);
lean_dec(x_28);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_82 = x_77;
} else {
 lean_dec_ref(x_77);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 0, x_40);
x_9 = x_45;
x_10 = x_48;
goto block_15;
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_45, 0);
x_85 = lean_ctor_get(x_45, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_45);
x_86 = l_Lean_NameSet_contains(x_84, x_34);
lean_dec(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; lean_object* x_98; size_t x_99; lean_object* x_100; 
x_87 = lean_st_ref_take(x_44, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_NameSet_insert(x_88, x_34);
x_91 = lean_st_ref_set(x_44, x_90, x_89);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_array_fget(x_38, x_29);
lean_dec(x_29);
lean_dec(x_38);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_box(0);
x_97 = lean_array_size(x_95);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_usize_of_nat(x_98);
x_100 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(x_42, x_1, x_2, x_95, x_97, x_99, x_96, x_7, x_92);
lean_dec(x_95);
lean_dec(x_42);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
if (lean_is_scalar(x_93)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_93;
}
lean_ctor_set(x_102, 0, x_40);
lean_ctor_set(x_102, 1, x_28);
x_9 = x_102;
x_10 = x_101;
goto block_15;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_93);
lean_dec(x_40);
lean_dec(x_28);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_105 = x_100;
} else {
 lean_dec_ref(x_100);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_40);
lean_ctor_set(x_107, 1, x_28);
x_9 = x_107;
x_10 = x_85;
goto block_15;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_40);
lean_ctor_set(x_108, 1, x_28);
x_9 = x_108;
x_10 = x_37;
goto block_15;
}
}
else
{
lean_object* x_109; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_40);
lean_ctor_set(x_109, 1, x_28);
x_9 = x_109;
x_10 = x_37;
goto block_15;
}
}
else
{
uint8_t x_110; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
x_110 = !lean_is_exclusive(x_35);
if (x_110 == 0)
{
return x_35;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_35, 0);
x_112 = lean_ctor_get(x_35, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_35);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_5, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3_spec__3(x_1, x_2, x_3, x_4, x_13, x_9, x_7, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Attribute_Builtin_getIdent_x3f(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_15 = l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_9);
x_16 = lean_mk_string_unchecked("initialization function must have type `IO Unit`", 48, 48);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_17, x_3, x_4, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(0);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_22 = l___private_Lean_Compiler_InitAttr_0__Lean_isIOUnit(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_mk_string_unchecked("initialization function must have type `IO Unit`", 48, 48);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_24, x_3, x_4, x_20);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_29, x_30, x_3, x_4, x_28);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_35 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_33, x_3, x_4, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_ConstantInfo_type(x_37);
lean_dec(x_37);
x_40 = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(x_39);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_35);
lean_dec(x_7);
x_41 = lean_mk_string_unchecked("initialization function '", 25, 25);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = l_Lean_MessageData_ofName(x_33);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_43);
lean_ctor_set(x_31, 0, x_42);
x_44 = lean_mk_string_unchecked("' must have type of the form `IO <type>`", 40, 40);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_46, x_3, x_4, x_38);
lean_dec(x_4);
lean_dec(x_3);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
x_49 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_50 = lean_expr_eqv(x_49, x_48);
lean_dec(x_48);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_35);
x_51 = lean_mk_string_unchecked("initialization function '", 25, 25);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = l_Lean_MessageData_ofName(x_33);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_53);
lean_ctor_set(x_31, 0, x_52);
x_54 = lean_mk_string_unchecked("' type mismatch", 15, 15);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_31);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_56, x_3, x_4, x_38);
lean_dec(x_4);
lean_dec(x_3);
return x_57;
}
else
{
lean_free_object(x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_35, 0);
x_59 = lean_ctor_get(x_35, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_35);
x_60 = l_Lean_ConstantInfo_type(x_58);
lean_dec(x_58);
x_61 = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(x_60);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_7);
x_62 = lean_mk_string_unchecked("initialization function '", 25, 25);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = l_Lean_MessageData_ofName(x_33);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_64);
lean_ctor_set(x_31, 0, x_63);
x_65 = lean_mk_string_unchecked("' must have type of the form `IO <type>`", 40, 40);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_31);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_67, x_3, x_4, x_59);
lean_dec(x_4);
lean_dec(x_3);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
lean_dec(x_61);
x_70 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_71 = lean_expr_eqv(x_70, x_69);
lean_dec(x_69);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_mk_string_unchecked("initialization function '", 25, 25);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = l_Lean_MessageData_ofName(x_33);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_74);
lean_ctor_set(x_31, 0, x_73);
x_75 = lean_mk_string_unchecked("' type mismatch", 15, 15);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_31);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_77, x_3, x_4, x_59);
lean_dec(x_4);
lean_dec(x_3);
return x_78;
}
else
{
lean_object* x_79; 
lean_free_object(x_31);
lean_dec(x_4);
lean_dec(x_3);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_33);
lean_ctor_set(x_79, 1, x_59);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_35);
if (x_80 == 0)
{
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_35, 0);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_35);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_31, 0);
x_85 = lean_ctor_get(x_31, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_31);
lean_inc(x_84);
x_86 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_84, x_3, x_4, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = l_Lean_ConstantInfo_type(x_87);
lean_dec(x_87);
x_91 = l___private_Lean_Compiler_InitAttr_0__Lean_getIOTypeArg(x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_89);
lean_dec(x_7);
x_92 = lean_mk_string_unchecked("initialization function '", 25, 25);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = l_Lean_MessageData_ofName(x_84);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_mk_string_unchecked("' must have type of the form `IO <type>`", 40, 40);
x_97 = l_Lean_stringToMessageData(x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_98, x_3, x_4, x_88);
lean_dec(x_4);
lean_dec(x_3);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
lean_dec(x_91);
x_101 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_102 = lean_expr_eqv(x_101, x_100);
lean_dec(x_100);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_89);
x_103 = lean_mk_string_unchecked("initialization function '", 25, 25);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = l_Lean_MessageData_ofName(x_84);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked("' type mismatch", 15, 15);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_109, x_3, x_4, x_88);
lean_dec(x_4);
lean_dec(x_3);
return x_110;
}
else
{
lean_object* x_111; 
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_89)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_89;
}
lean_ctor_set(x_111, 0, x_84);
lean_ctor_set(x_111, 1, x_88);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_84);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_86, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_86, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_114 = x_86;
} else {
 lean_dec_ref(x_86);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_9);
if (x_116 == 0)
{
return x_9;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_9, 0);
x_118 = lean_ctor_get(x_9, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_9);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_6);
if (x_120 == 0)
{
return x_6;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_6, 0);
x_122 = lean_ctor_get(x_6, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_6);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_isInitializerExecutionEnabled(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
if (x_1 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
goto block_11;
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
if (x_12 == 0)
{
lean_dec(x_2);
goto block_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_8);
x_13 = lean_ctor_get(x_3, 0);
x_14 = l_Lean_Environment_header(x_13);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = l_Array_toSubarray___redArg(x_15, x_16, x_17);
x_19 = lean_array_get_size(x_2);
x_20 = l_Array_toSubarray___redArg(x_2, x_16, x_19);
x_21 = lean_ctor_get(x_14, 3);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_21);
x_24 = lean_usize_of_nat(x_16);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3(x_3, x_13, x_21, x_23, x_24, x_22, x_3, x_7);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_10 = lean_alloc_ctor(0, 2, 0);
} else {
 x_10 = x_8;
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_alloc_closure((void*)(l_Lean_registerInitAttrUnsafe___lam__0___boxed), 5, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_registerInitAttrUnsafe___lam__1), 5, 0);
x_7 = lean_box(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_registerInitAttrUnsafe___lam__2___boxed), 4, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("initialization procedure for global references", 46, 46);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_12);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_5);
lean_ctor_set(x_13, 3, x_8);
x_14 = l_Lean_registerParametricAttribute(lean_box(0), x_13, x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_registerInitAttrUnsafe_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1_spec__1(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__1(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3_spec__3(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_registerInitAttrUnsafe_spec__3(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_registerInitAttrUnsafe___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_registerInitAttrUnsafe___lam__2(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttrUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_registerInitAttrUnsafe(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_InitAttr___hyg_1133_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("declName", 8, 8);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_20 = l_Lean_mkAtom(x_19);
lean_inc(x_7);
x_21 = lean_array_push(x_7, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerInitAttrUnsafe(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInitAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_registerInitAttr(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_1146_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("init", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("regularInitAttr", 15, 15);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unbox(x_4);
x_9 = l_Lean_registerInitAttrUnsafe(x_3, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_1174_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("builtin_init", 12, 12);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("builtinInitAttr", 15, 15);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_unbox(x_4);
x_9 = l_Lean_registerInitAttrUnsafe(x_3, x_8, x_7, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getInitFnNameForCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_4, x_2, x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_dec(x_6);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getInitFnNameForCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getInitFnNameForCore_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_get_builtin_init_fn_name_for(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_builtinInitAttr;
x_4 = l_Lean_getInitFnNameForCore_x3f(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_get_regular_init_fn_name_for(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_regularInitAttr;
x_4 = l_Lean_getInitFnNameForCore_x3f(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_get_init_fn_name_for(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_get_builtin_init_fn_name_for(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_get_regular_init_fn_name_for(x_1, x_2);
return x_4;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_Lean_isIOUnitInitFnCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_4, x_2, x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIOUnitInitFnCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_isIOUnitInitFnCore(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lean_is_io_unit_regular_init_fn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_regularInitAttr;
x_4 = l_Lean_isIOUnitInitFnCore(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isIOUnitRegularInitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_io_unit_regular_init_fn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lean_is_io_unit_builtin_init_fn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_builtinInitAttr;
x_4 = l_Lean_isIOUnitInitFnCore(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isIOUnitBuiltinInitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_io_unit_builtin_init_fn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isIOUnitInitFn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lean_is_io_unit_builtin_init_fn(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_is_io_unit_regular_init_fn(x_1, x_2);
return x_4;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIOUnitInitFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isIOUnitInitFn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_hasInitAttr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_init_fn_name_for(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_hasInitAttr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_hasInitAttr(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setBuiltinInitAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_builtinInitAttr;
x_5 = l_Lean_ParametricAttribute_setParam___redArg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(x_8, x_1, x_2);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(x_12, x_1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_declareBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_mk_string_unchecked("_regBuiltin", 11, 11);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Name_append(x_7, x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___redArg(x_8, x_9, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_mk_string_unchecked("IO", 2, 2);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Unit", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_16);
x_21 = l_Lean_Expr_app___override(x_17, x_20);
x_22 = lean_box(0);
lean_inc(x_12);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_box(0);
x_25 = lean_box(1);
lean_inc(x_12);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_22);
x_26 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_10);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
lean_inc(x_4);
lean_inc(x_3);
x_29 = l_Lean_addAndCompile(x_28, x_3, x_4, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_get(x_4, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = l_Lean_setBuiltinInitAttr(x_35, x_12, x_36);
x_38 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_37, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_31);
lean_dec(x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_39, x_4, x_40);
lean_dec(x_4);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_3, 5);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_io_error_to_string(x_43);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_MessageData_ofFormat(x_46);
lean_ctor_set(x_31, 1, x_47);
lean_ctor_set(x_31, 0, x_44);
lean_ctor_set(x_38, 0, x_31);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_38);
x_50 = lean_ctor_get(x_3, 5);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_io_error_to_string(x_48);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_MessageData_ofFormat(x_52);
lean_ctor_set(x_31, 1, x_53);
lean_ctor_set(x_31, 0, x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_31);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_box(0);
x_59 = l_Lean_setBuiltinInitAttr(x_57, x_12, x_58);
x_60 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_59, x_56);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_61, x_4, x_62);
lean_dec(x_4);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_3, 5);
lean_inc(x_67);
lean_dec(x_3);
x_68 = lean_io_error_to_string(x_64);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_MessageData_ofFormat(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_66)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_66;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
return x_72;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_73 = lean_ctor_get(x_10, 0);
x_74 = lean_ctor_get(x_10, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_10);
x_75 = lean_mk_string_unchecked("IO", 2, 2);
x_76 = l_Lean_Name_mkStr1(x_75);
x_77 = lean_box(0);
x_78 = l_Lean_Expr_const___override(x_76, x_77);
x_79 = lean_mk_string_unchecked("Unit", 4, 4);
x_80 = l_Lean_Name_mkStr1(x_79);
x_81 = l_Lean_Expr_const___override(x_80, x_77);
x_82 = l_Lean_Expr_app___override(x_78, x_81);
x_83 = lean_box(0);
lean_inc(x_73);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_82);
x_85 = lean_box(0);
x_86 = lean_box(1);
lean_inc(x_73);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_83);
x_88 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_2);
lean_ctor_set(x_88, 2, x_85);
lean_ctor_set(x_88, 3, x_87);
x_89 = lean_unbox(x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_89);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_88);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l_Lean_addAndCompile(x_90, x_3, x_4, x_74);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_st_ref_get(x_4, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_box(0);
x_99 = l_Lean_setBuiltinInitAttr(x_97, x_73, x_98);
x_100 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_99, x_95);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_96);
lean_dec(x_3);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_setEnv___at___Lean_compileDecls_doCompile_spec__9___redArg(x_101, x_4, x_102);
lean_dec(x_4);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_106 = x_100;
} else {
 lean_dec_ref(x_100);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_3, 5);
lean_inc(x_107);
lean_dec(x_3);
x_108 = lean_io_error_to_string(x_104);
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l_Lean_MessageData_ofFormat(x_109);
if (lean_is_scalar(x_96)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_96;
}
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_106;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_105);
return x_112;
}
}
else
{
lean_dec(x_73);
lean_dec(x_4);
lean_dec(x_3);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkAuxName___at___Lean_declareBuiltin_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_218_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_interpretedModInits = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_interpretedModInits);
lean_dec_ref(res);
}l___auto____x40_Lean_Compiler_InitAttr___hyg_1133_ = _init_l___auto____x40_Lean_Compiler_InitAttr___hyg_1133_();
lean_mark_persistent(l___auto____x40_Lean_Compiler_InitAttr___hyg_1133_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_1146_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_regularInitAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_regularInitAttr);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_1174_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_builtinInitAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_builtinInitAttr);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
