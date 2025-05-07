// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: Lean.Compiler.IR.CompilerM Lean.Compiler.IR.Format
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_usize_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_usizeSize;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorScalarsSize;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___redArg(lean_object*, lean_object*);
lean_object* lean_get_max_ctor_fields(lean_object*);
lean_object* lean_get_max_ctor_tag(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkFullApp___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__6(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorTag;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_ExceptT_bindCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkExpr___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__11(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Checker_getDecl___lam__0(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_2, x_1, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_mk_string_unchecked("variable / joinpoint index ", 27, 27);
x_14 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked(" has already been used", 22, 22);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_17);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_18 = lean_mk_string_unchecked("variable / joinpoint index ", 27, 27);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked(" has already been used", 22, 22);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_25 = x_24;
} else {
 lean_dec_ref(x_24);
 x_25 = lean_box(0);
}
x_26 = lean_mk_string_unchecked("variable / joinpoint index ", 27, 27);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked(" has already been used", 22, 22);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
if (lean_is_scalar(x_25)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_25;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_getDecl___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl___lam__0___boxed), 1, 0);
x_8 = lean_mk_string_unchecked("depends on declaration '", 24, 24);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_1, x_10, x_7);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("', which has no executable code; consider marking definition as 'noncomputable'", 79, 79);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Checker_getDecl___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = l_Lean_IR_LocalContext_isLocalVar(x_18, x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_IR_LocalContext_isParam(x_18, x_1);
x_4 = x_20;
goto block_17;
}
else
{
x_4 = x_19;
goto block_17;
}
block_17:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_mk_string_unchecked("unknown variable '", 18, 18);
x_6 = lean_mk_string_unchecked("x_", 2, 2);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_5, x_8);
lean_dec(x_8);
x_10 = lean_mk_string_unchecked("'", 1, 1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_isJP(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_mk_string_unchecked("unknown join point '", 20, 20);
x_7 = lean_mk_string_unchecked("block_", 6, 6);
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("'", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_Checker_checkVar(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_Checker_checkArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_10);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_6 = x_11;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_13, x_14, x_6, x_2, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_beq(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_beq(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkEqTypes___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkEqTypes(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_10 = lean_apply_1(x_2, x_1);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_13 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_14 = lean_unsigned_to_nat(120u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_format_pretty(x_13, x_14, x_15, x_15);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("'", 1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_19; 
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_5 = x_19;
x_6 = x_4;
goto block_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_22 = lean_mk_string_unchecked(", ", 2, 2);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_string_append(x_23, x_20);
x_5 = x_24;
x_6 = x_4;
goto block_9;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = lean_apply_1(x_2, x_1);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_14 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_15 = lean_unsigned_to_nat(120u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_format_pretty(x_14, x_15, x_16, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("'", 1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_20; 
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_6 = x_20;
x_7 = x_5;
goto block_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_23 = lean_mk_string_unchecked(", ", 2, 2);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_24, x_21);
x_6 = x_25;
x_7 = x_5;
goto block_10;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkType___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isObj(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_mk_string_unchecked("object expected", 15, 15);
x_5 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_6 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_7 = lean_unsigned_to_nat(120u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("'", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked(", ", 2, 2);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_14, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isScalar(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_mk_string_unchecked("scalar expected", 15, 15);
x_5 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_6 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_7 = lean_unsigned_to_nat(120u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("'", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked(", ", 2, 2);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_14, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarType___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_getType(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_mk_string_unchecked("unknown variable '", 18, 18);
x_7 = lean_mk_string_unchecked("x_", 2, 2);
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("'", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_IR_Checker_getType(x_1, x_4, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_20 = x_12;
} else {
 lean_dec_ref(x_12);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
x_28 = lean_apply_1(x_2, x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_12);
lean_free_object(x_11);
x_30 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_31 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_27);
x_32 = lean_unsigned_to_nat(120u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_format_pretty(x_31, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked("'", 1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_37; 
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_6 = x_37;
x_7 = x_24;
goto block_10;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_40 = lean_mk_string_unchecked(", ", 2, 2);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = lean_string_append(x_41, x_38);
x_6 = x_42;
x_7 = x_24;
goto block_10;
}
}
else
{
lean_object* x_43; 
lean_dec(x_27);
x_43 = lean_box(0);
lean_ctor_set(x_12, 0, x_43);
return x_11;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_44);
lean_dec(x_12);
lean_inc(x_44);
x_45 = lean_apply_1(x_2, x_44);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_11);
x_47 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_48 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_44);
x_49 = lean_unsigned_to_nat(120u);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_format_pretty(x_48, x_49, x_50, x_50);
x_52 = lean_string_append(x_47, x_51);
lean_dec(x_51);
x_53 = lean_mk_string_unchecked("'", 1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_54; 
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_6 = x_54;
x_7 = x_24;
goto block_10;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_3, 0);
x_56 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_57 = lean_mk_string_unchecked(", ", 2, 2);
x_58 = lean_string_append(x_56, x_57);
lean_dec(x_57);
x_59 = lean_string_append(x_58, x_55);
x_6 = x_59;
x_7 = x_24;
goto block_10;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_44);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_11, 0, x_61);
return x_11;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_dec(x_11);
x_63 = lean_ctor_get(x_12, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_64 = x_12;
} else {
 lean_dec_ref(x_12);
 x_64 = lean_box(0);
}
lean_inc(x_63);
x_65 = lean_apply_1(x_2, x_63);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_64);
x_67 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_68 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_63);
x_69 = lean_unsigned_to_nat(120u);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_format_pretty(x_68, x_69, x_70, x_70);
x_72 = lean_string_append(x_67, x_71);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("'", 1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_74; 
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_6 = x_74;
x_7 = x_62;
goto block_10;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_3, 0);
x_76 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_77 = lean_mk_string_unchecked(", ", 2, 2);
x_78 = lean_string_append(x_76, x_77);
lean_dec(x_77);
x_79 = lean_string_append(x_78, x_75);
x_6 = x_79;
x_7 = x_62;
goto block_10;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_63);
x_80 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_64;
}
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
return x_82;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = l_Lean_IR_IRType_isObj(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_mk_string_unchecked("object expected", 15, 15);
x_22 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_23 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_24 = lean_unsigned_to_nat(120u);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_format_pretty(x_23, x_24, x_25, x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("'", 1, 1);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked(", ", 2, 2);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_string_append(x_31, x_21);
lean_dec(x_21);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; 
lean_dec(x_19);
x_33 = lean_box(0);
lean_ctor_set(x_5, 0, x_33);
return x_4;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_IR_IRType_isObj(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_mk_string_unchecked("object expected", 15, 15);
x_37 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_38 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_34);
x_39 = lean_unsigned_to_nat(120u);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_format_pretty(x_38, x_39, x_40, x_40);
x_42 = lean_string_append(x_37, x_41);
lean_dec(x_41);
x_43 = lean_mk_string_unchecked("'", 1, 1);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked(", ", 2, 2);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = lean_string_append(x_46, x_36);
lean_dec(x_36);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_4, 0, x_48);
return x_4;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_34);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_4, 0, x_50);
return x_4;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
lean_dec(x_4);
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_53 = x_5;
} else {
 lean_dec_ref(x_5);
 x_53 = lean_box(0);
}
x_54 = l_Lean_IR_IRType_isObj(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_mk_string_unchecked("object expected", 15, 15);
x_56 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_57 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_52);
x_58 = lean_unsigned_to_nat(120u);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_format_pretty(x_57, x_58, x_59, x_59);
x_61 = lean_string_append(x_56, x_60);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("'", 1, 1);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(", ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_55);
lean_dec(x_55);
if (lean_is_scalar(x_53)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_53;
 lean_ctor_set_tag(x_67, 0);
}
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_51);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
x_69 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_53;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_51);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = l_Lean_IR_IRType_isScalar(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_mk_string_unchecked("scalar expected", 15, 15);
x_22 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_23 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_24 = lean_unsigned_to_nat(120u);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_format_pretty(x_23, x_24, x_25, x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("'", 1, 1);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked(", ", 2, 2);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_string_append(x_31, x_21);
lean_dec(x_21);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; 
lean_dec(x_19);
x_33 = lean_box(0);
lean_ctor_set(x_5, 0, x_33);
return x_4;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_IR_IRType_isScalar(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_mk_string_unchecked("scalar expected", 15, 15);
x_37 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_38 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_34);
x_39 = lean_unsigned_to_nat(120u);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_format_pretty(x_38, x_39, x_40, x_40);
x_42 = lean_string_append(x_37, x_41);
lean_dec(x_41);
x_43 = lean_mk_string_unchecked("'", 1, 1);
x_44 = lean_string_append(x_42, x_43);
lean_dec(x_43);
x_45 = lean_mk_string_unchecked(", ", 2, 2);
x_46 = lean_string_append(x_44, x_45);
lean_dec(x_45);
x_47 = lean_string_append(x_46, x_36);
lean_dec(x_36);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_4, 0, x_48);
return x_4;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_34);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_4, 0, x_50);
return x_4;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
lean_dec(x_4);
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_53 = x_5;
} else {
 lean_dec_ref(x_5);
 x_53 = lean_box(0);
}
x_54 = l_Lean_IR_IRType_isScalar(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_mk_string_unchecked("scalar expected", 15, 15);
x_56 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_57 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_52);
x_58 = lean_unsigned_to_nat(120u);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_format_pretty(x_57, x_58, x_59, x_59);
x_61 = lean_string_append(x_56, x_60);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("'", 1, 1);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(", ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_55);
lean_dec(x_55);
if (lean_is_scalar(x_53)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_53;
 lean_ctor_set_tag(x_67, 0);
}
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_51);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
x_69 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_53;
}
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_51);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkFullApp___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_46; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_18 = x_5;
} else {
 lean_dec_ref(x_5);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_21 = lean_array_get_size(x_2);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_dec(x_19);
x_22 = x_46;
goto block_45;
block_45:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_eq(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_3);
x_25 = lean_box(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkFullApp___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_mk_string_unchecked("incorrect number of arguments to '", 34, 34);
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Name_toString(x_1, x_29, x_26);
x_31 = lean_string_append(x_27, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("', ", 3, 3);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l___private_Init_Data_Repr_0__Nat_reprFast(x_21);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked(" provided, ", 11, 11);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_mk_string_unchecked(" expected", 9, 9);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
if (lean_is_scalar(x_20)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_20;
 lean_ctor_set_tag(x_42, 0);
}
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_18)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_18;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_17);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
x_44 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_17);
lean_dec(x_3);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Checker_checkFullApp___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_43; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_18 = x_5;
} else {
 lean_dec_ref(x_5);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl___lam__0___boxed), 1, 0);
x_22 = lean_array_get_size(x_2);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_dec(x_19);
x_23 = x_43;
goto block_42;
block_42:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_nat_dec_lt(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_26 = lean_mk_string_unchecked("too many arguments too partial application '", 44, 44);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
x_29 = l_Lean_Name_toString(x_1, x_28, x_21);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("', num. args: ", 14, 14);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_mk_string_unchecked(", arity: ", 9, 9);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_24);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
if (lean_is_scalar(x_20)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_20;
 lean_ctor_set_tag(x_39, 0);
}
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_18)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_18;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_17);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
x_41 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_17);
lean_dec(x_3);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkExpr___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_28; uint8_t x_67; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_16 = x_2;
} else {
 lean_dec_ref(x_2);
 x_16 = lean_box(0);
}
x_17 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl___lam__0___boxed), 1, 0);
x_72 = l_Lean_IR_Checker_maxCtorTag;
x_73 = lean_ctor_get(x_14, 1);
lean_inc(x_73);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
x_28 = x_74;
goto block_66;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_ctor_get(x_14, 2);
lean_inc(x_76);
x_77 = lean_nat_dec_lt(x_75, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_14, 3);
lean_inc(x_78);
x_79 = lean_nat_dec_lt(x_75, x_78);
lean_dec(x_78);
x_67 = x_79;
goto block_71;
}
else
{
x_67 = x_77;
goto block_71;
}
}
block_27:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_mk_string_unchecked("tag for constructor '", 21, 21);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Name_toString(x_20, x_18, x_17);
x_22 = lean_string_append(x_19, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("' is too big, this is a limitation of the current runtime", 57, 57);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_is_scalar(x_16)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_16;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
block_66:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_16);
x_29 = l_Lean_IR_Checker_maxCtorFields;
x_30 = lean_ctor_get(x_14, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = l_Lean_IR_Checker_maxCtorScalarsSize;
x_33 = lean_ctor_get(x_14, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 3);
lean_inc(x_34);
x_35 = l_Lean_IR_Checker_usizeSize;
x_36 = lean_nat_mul(x_34, x_35);
lean_dec(x_34);
x_37 = lean_nat_add(x_33, x_36);
lean_dec(x_36);
lean_dec(x_33);
x_38 = lean_nat_dec_lt(x_32, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_IR_IRType_isStruct(x_1);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_IR_IRType_isUnion(x_1);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_IR_CtorInfo_isRef(x_14);
lean_dec(x_14);
if (x_41 == 0)
{
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_4);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_3);
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_IR_Checker_checkArgs(x_15, x_3, x_44);
lean_dec(x_3);
lean_dec(x_15);
return x_45;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
goto block_13;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
goto block_13;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_box(x_28);
x_47 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkExpr___lam__1___boxed), 2, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = lean_mk_string_unchecked("constructor '", 13, 13);
x_49 = lean_ctor_get(x_14, 0);
lean_inc(x_49);
lean_dec(x_14);
x_50 = l_Lean_Name_toString(x_49, x_38, x_47);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("' has too many scalar fields", 28, 28);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_56 = lean_box(x_28);
x_57 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkExpr___lam__1___boxed), 2, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_mk_string_unchecked("constructor '", 13, 13);
x_59 = lean_ctor_get(x_14, 0);
lean_inc(x_59);
lean_dec(x_14);
x_60 = l_Lean_Name_toString(x_59, x_31, x_57);
x_61 = lean_string_append(x_58, x_60);
lean_dec(x_60);
x_62 = lean_mk_string_unchecked("' has too many fields", 21, 21);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_4);
return x_65;
}
}
else
{
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_18 = x_28;
goto block_27;
}
}
block_71:
{
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_ctor_get(x_14, 4);
lean_inc(x_69);
x_70 = lean_nat_dec_lt(x_68, x_69);
lean_dec(x_69);
x_28 = x_70;
goto block_66;
}
else
{
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_18 = x_67;
goto block_27;
}
}
}
case 1:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
lean_dec(x_2);
x_81 = l_Lean_IR_Checker_checkObjVar(x_80, x_3, x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_dec(x_82);
lean_dec(x_1);
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_83);
return x_84;
}
}
case 2:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
lean_dec(x_2);
x_87 = l_Lean_IR_Checker_checkObjVar(x_85, x_3, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_3);
x_5 = x_87;
goto block_9;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_IR_Checker_checkArgs(x_86, x_3, x_89);
lean_dec(x_3);
lean_dec(x_86);
x_5 = x_90;
goto block_9;
}
}
case 3:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
lean_dec(x_2);
x_93 = l_Lean_IR_Checker_getType(x_92, x_3, x_4);
lean_dec(x_3);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_91);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_93, 0, x_99);
return x_93;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
return x_104;
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_94);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_94, 0);
switch (lean_obj_tag(x_106)) {
case 7:
{
lean_object* x_107; lean_object* x_108; 
lean_free_object(x_94);
lean_dec(x_91);
x_107 = lean_ctor_get(x_93, 1);
lean_inc(x_107);
lean_dec(x_93);
x_108 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_107);
return x_108;
}
case 8:
{
lean_object* x_109; lean_object* x_110; 
lean_free_object(x_94);
lean_dec(x_91);
x_109 = lean_ctor_get(x_93, 1);
lean_inc(x_109);
lean_dec(x_93);
x_110 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_109);
return x_110;
}
case 10:
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_93);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_93, 0);
lean_dec(x_112);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_dec(x_106);
x_114 = lean_array_get_size(x_113);
x_115 = lean_nat_dec_lt(x_91, x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_dec(x_91);
lean_dec(x_1);
x_116 = lean_mk_string_unchecked("invalid proj index", 18, 18);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_116);
return x_93;
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_array_fget(x_113, x_91);
lean_dec(x_91);
lean_dec(x_113);
x_118 = l_Lean_IR_IRType_beq(x_117, x_1);
lean_dec(x_1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_119);
return x_93;
}
else
{
lean_object* x_120; 
x_120 = lean_box(0);
lean_ctor_set(x_94, 0, x_120);
return x_93;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_93, 1);
lean_inc(x_121);
lean_dec(x_93);
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
lean_dec(x_106);
x_123 = lean_array_get_size(x_122);
x_124 = lean_nat_dec_lt(x_91, x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_122);
lean_dec(x_91);
lean_dec(x_1);
x_125 = lean_mk_string_unchecked("invalid proj index", 18, 18);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_125);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_94);
lean_ctor_set(x_126, 1, x_121);
return x_126;
}
else
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_array_fget(x_122, x_91);
lean_dec(x_91);
lean_dec(x_122);
x_128 = l_Lean_IR_IRType_beq(x_127, x_1);
lean_dec(x_1);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_129);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_94);
lean_ctor_set(x_130, 1, x_121);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_box(0);
lean_ctor_set(x_94, 0, x_131);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_94);
lean_ctor_set(x_132, 1, x_121);
return x_132;
}
}
}
}
case 11:
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_93);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_93, 0);
lean_dec(x_134);
x_135 = lean_ctor_get(x_106, 1);
lean_inc(x_135);
lean_dec(x_106);
x_136 = lean_array_get_size(x_135);
x_137 = lean_nat_dec_lt(x_91, x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_91);
lean_dec(x_1);
x_138 = lean_mk_string_unchecked("invalid proj index", 18, 18);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_138);
return x_93;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_array_fget(x_135, x_91);
lean_dec(x_91);
lean_dec(x_135);
x_140 = l_Lean_IR_IRType_beq(x_139, x_1);
lean_dec(x_1);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_141);
return x_93;
}
else
{
lean_object* x_142; 
x_142 = lean_box(0);
lean_ctor_set(x_94, 0, x_142);
return x_93;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_ctor_get(x_93, 1);
lean_inc(x_143);
lean_dec(x_93);
x_144 = lean_ctor_get(x_106, 1);
lean_inc(x_144);
lean_dec(x_106);
x_145 = lean_array_get_size(x_144);
x_146 = lean_nat_dec_lt(x_91, x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_144);
lean_dec(x_91);
lean_dec(x_1);
x_147 = lean_mk_string_unchecked("invalid proj index", 18, 18);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_147);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_94);
lean_ctor_set(x_148, 1, x_143);
return x_148;
}
else
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_array_fget(x_144, x_91);
lean_dec(x_91);
lean_dec(x_144);
x_150 = l_Lean_IR_IRType_beq(x_149, x_1);
lean_dec(x_1);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_151);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_94);
lean_ctor_set(x_152, 1, x_143);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_box(0);
lean_ctor_set(x_94, 0, x_153);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_94);
lean_ctor_set(x_154, 1, x_143);
return x_154;
}
}
}
}
default: 
{
uint8_t x_155; 
lean_dec(x_91);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_93);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_156 = lean_ctor_get(x_93, 0);
lean_dec(x_156);
x_157 = lean_mk_string_unchecked("unexpected IR type '", 20, 20);
x_158 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_106);
x_159 = lean_unsigned_to_nat(120u);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_format_pretty(x_158, x_159, x_160, x_160);
x_162 = lean_string_append(x_157, x_161);
lean_dec(x_161);
x_163 = lean_mk_string_unchecked("'", 1, 1);
x_164 = lean_string_append(x_162, x_163);
lean_dec(x_163);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_164);
return x_93;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_93, 1);
lean_inc(x_165);
lean_dec(x_93);
x_166 = lean_mk_string_unchecked("unexpected IR type '", 20, 20);
x_167 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_106);
x_168 = lean_unsigned_to_nat(120u);
x_169 = lean_unsigned_to_nat(0u);
x_170 = lean_format_pretty(x_167, x_168, x_169, x_169);
x_171 = lean_string_append(x_166, x_170);
lean_dec(x_170);
x_172 = lean_mk_string_unchecked("'", 1, 1);
x_173 = lean_string_append(x_171, x_172);
lean_dec(x_172);
lean_ctor_set_tag(x_94, 0);
lean_ctor_set(x_94, 0, x_173);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_94);
lean_ctor_set(x_174, 1, x_165);
return x_174;
}
}
}
}
else
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_94, 0);
lean_inc(x_175);
lean_dec(x_94);
switch (lean_obj_tag(x_175)) {
case 7:
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_91);
x_176 = lean_ctor_get(x_93, 1);
lean_inc(x_176);
lean_dec(x_93);
x_177 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_176);
return x_177;
}
case 8:
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_91);
x_178 = lean_ctor_get(x_93, 1);
lean_inc(x_178);
lean_dec(x_93);
x_179 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_178);
return x_179;
}
case 10:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_180 = lean_ctor_get(x_93, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_181 = x_93;
} else {
 lean_dec_ref(x_93);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_175, 1);
lean_inc(x_182);
lean_dec(x_175);
x_183 = lean_array_get_size(x_182);
x_184 = lean_nat_dec_lt(x_91, x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_182);
lean_dec(x_91);
lean_dec(x_1);
x_185 = lean_mk_string_unchecked("invalid proj index", 18, 18);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
if (lean_is_scalar(x_181)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_181;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_180);
return x_187;
}
else
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_array_fget(x_182, x_91);
lean_dec(x_91);
lean_dec(x_182);
x_189 = l_Lean_IR_IRType_beq(x_188, x_1);
lean_dec(x_1);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_190);
if (lean_is_scalar(x_181)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_181;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_180);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
if (lean_is_scalar(x_181)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_181;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_180);
return x_195;
}
}
}
case 11:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_93, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_197 = x_93;
} else {
 lean_dec_ref(x_93);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_175, 1);
lean_inc(x_198);
lean_dec(x_175);
x_199 = lean_array_get_size(x_198);
x_200 = lean_nat_dec_lt(x_91, x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_198);
lean_dec(x_91);
lean_dec(x_1);
x_201 = lean_mk_string_unchecked("invalid proj index", 18, 18);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
if (lean_is_scalar(x_197)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_197;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_196);
return x_203;
}
else
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_array_fget(x_198, x_91);
lean_dec(x_91);
lean_dec(x_198);
x_205 = l_Lean_IR_IRType_beq(x_204, x_1);
lean_dec(x_1);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
if (lean_is_scalar(x_197)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_197;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_196);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
if (lean_is_scalar(x_197)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_197;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_196);
return x_211;
}
}
}
default: 
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_91);
lean_dec(x_1);
x_212 = lean_ctor_get(x_93, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_213 = x_93;
} else {
 lean_dec_ref(x_93);
 x_213 = lean_box(0);
}
x_214 = lean_mk_string_unchecked("unexpected IR type '", 20, 20);
x_215 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_175);
x_216 = lean_unsigned_to_nat(120u);
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_format_pretty(x_215, x_216, x_217, x_217);
x_219 = lean_string_append(x_214, x_218);
lean_dec(x_218);
x_220 = lean_mk_string_unchecked("'", 1, 1);
x_221 = lean_string_append(x_219, x_220);
lean_dec(x_220);
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_213)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_213;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_212);
return x_223;
}
}
}
}
}
case 4:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_2, 1);
lean_inc(x_224);
lean_dec(x_2);
x_225 = l_Lean_IR_Checker_checkObjVar(x_224, x_3, x_4);
lean_dec(x_3);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_dec(x_226);
lean_dec(x_1);
return x_225;
}
else
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_225);
if (x_227 == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_225, 0);
lean_dec(x_228);
x_229 = !lean_is_exclusive(x_226);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_226, 0);
lean_dec(x_230);
x_231 = lean_box(5);
x_232 = l_Lean_IR_IRType_beq(x_1, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_233 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_234 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_235 = lean_unsigned_to_nat(120u);
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_format_pretty(x_234, x_235, x_236, x_236);
x_238 = lean_string_append(x_233, x_237);
lean_dec(x_237);
x_239 = lean_mk_string_unchecked("'", 1, 1);
x_240 = lean_string_append(x_238, x_239);
lean_dec(x_239);
lean_ctor_set_tag(x_226, 0);
lean_ctor_set(x_226, 0, x_240);
return x_225;
}
else
{
lean_object* x_241; 
lean_dec(x_1);
x_241 = lean_box(0);
lean_ctor_set(x_226, 0, x_241);
return x_225;
}
}
else
{
lean_object* x_242; uint8_t x_243; 
lean_dec(x_226);
x_242 = lean_box(5);
x_243 = l_Lean_IR_IRType_beq(x_1, x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_244 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_245 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_246 = lean_unsigned_to_nat(120u);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_format_pretty(x_245, x_246, x_247, x_247);
x_249 = lean_string_append(x_244, x_248);
lean_dec(x_248);
x_250 = lean_mk_string_unchecked("'", 1, 1);
x_251 = lean_string_append(x_249, x_250);
lean_dec(x_250);
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_225, 0, x_252);
return x_225;
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_1);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_225, 0, x_254);
return x_225;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_255 = lean_ctor_get(x_225, 1);
lean_inc(x_255);
lean_dec(x_225);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_256 = x_226;
} else {
 lean_dec_ref(x_226);
 x_256 = lean_box(0);
}
x_257 = lean_box(5);
x_258 = l_Lean_IR_IRType_beq(x_1, x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_259 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_260 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_261 = lean_unsigned_to_nat(120u);
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_format_pretty(x_260, x_261, x_262, x_262);
x_264 = lean_string_append(x_259, x_263);
lean_dec(x_263);
x_265 = lean_mk_string_unchecked("'", 1, 1);
x_266 = lean_string_append(x_264, x_265);
lean_dec(x_265);
if (lean_is_scalar(x_256)) {
 x_267 = lean_alloc_ctor(0, 1, 0);
} else {
 x_267 = x_256;
 lean_ctor_set_tag(x_267, 0);
}
lean_ctor_set(x_267, 0, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_255);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_1);
x_269 = lean_box(0);
if (lean_is_scalar(x_256)) {
 x_270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_270 = x_256;
}
lean_ctor_set(x_270, 0, x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_255);
return x_271;
}
}
}
}
case 5:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_2, 2);
lean_inc(x_272);
lean_dec(x_2);
x_273 = l_Lean_IR_Checker_checkObjVar(x_272, x_3, x_4);
lean_dec(x_3);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_dec(x_274);
lean_dec(x_1);
return x_273;
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_IR_Checker_checkScalarType___redArg(x_1, x_275);
return x_276;
}
}
case 6:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_1);
x_277 = lean_ctor_get(x_2, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_2, 1);
lean_inc(x_278);
lean_dec(x_2);
x_279 = l_Lean_IR_Checker_checkFullApp(x_277, x_278, x_3, x_4);
lean_dec(x_278);
return x_279;
}
case 7:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = lean_ctor_get(x_2, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_2, 1);
lean_inc(x_281);
lean_dec(x_2);
x_282 = l_Lean_IR_Checker_checkPartialApp(x_280, x_281, x_3, x_4);
lean_dec(x_281);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
if (lean_obj_tag(x_283) == 0)
{
lean_dec(x_283);
lean_dec(x_1);
return x_282;
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_284);
return x_285;
}
}
case 8:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_1);
x_286 = lean_ctor_get(x_2, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_2, 1);
lean_inc(x_287);
lean_dec(x_2);
x_288 = l_Lean_IR_Checker_checkObjVar(x_286, x_3, x_4);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_dec(x_289);
lean_dec(x_287);
lean_dec(x_3);
return x_288;
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = l_Lean_IR_Checker_checkArgs(x_287, x_3, x_290);
lean_dec(x_3);
lean_dec(x_287);
return x_291;
}
}
case 9:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_354; lean_object* x_355; 
x_292 = lean_ctor_get(x_2, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_2, 1);
lean_inc(x_293);
lean_dec(x_2);
x_354 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_4);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_dec(x_355);
x_294 = x_354;
goto block_353;
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
lean_inc(x_293);
x_357 = l_Lean_IR_Checker_checkScalarVar(x_293, x_3, x_356);
x_294 = x_357;
goto block_353;
}
block_353:
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 0)
{
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_3);
return x_294;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = l_Lean_IR_Checker_getType(x_293, x_3, x_296);
lean_dec(x_3);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
if (lean_obj_tag(x_298) == 0)
{
uint8_t x_299; 
lean_dec(x_292);
x_299 = !lean_is_exclusive(x_297);
if (x_299 == 0)
{
lean_object* x_300; uint8_t x_301; 
x_300 = lean_ctor_get(x_297, 0);
lean_dec(x_300);
x_301 = !lean_is_exclusive(x_298);
if (x_301 == 0)
{
return x_297;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_298, 0);
lean_inc(x_302);
lean_dec(x_298);
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_297, 0, x_303);
return x_297;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_304 = lean_ctor_get(x_297, 1);
lean_inc(x_304);
lean_dec(x_297);
x_305 = lean_ctor_get(x_298, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_306 = x_298;
} else {
 lean_dec_ref(x_298);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(0, 1, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_305);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_304);
return x_308;
}
}
else
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_297);
if (x_309 == 0)
{
lean_object* x_310; uint8_t x_311; 
x_310 = lean_ctor_get(x_297, 0);
lean_dec(x_310);
x_311 = !lean_is_exclusive(x_298);
if (x_311 == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_298, 0);
x_313 = l_Lean_IR_IRType_beq(x_312, x_292);
lean_dec(x_292);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_314 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_315 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_312);
x_316 = lean_unsigned_to_nat(120u);
x_317 = lean_unsigned_to_nat(0u);
x_318 = lean_format_pretty(x_315, x_316, x_317, x_317);
x_319 = lean_string_append(x_314, x_318);
lean_dec(x_318);
x_320 = lean_mk_string_unchecked("'", 1, 1);
x_321 = lean_string_append(x_319, x_320);
lean_dec(x_320);
lean_ctor_set_tag(x_298, 0);
lean_ctor_set(x_298, 0, x_321);
return x_297;
}
else
{
lean_object* x_322; 
lean_dec(x_312);
x_322 = lean_box(0);
lean_ctor_set(x_298, 0, x_322);
return x_297;
}
}
else
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_ctor_get(x_298, 0);
lean_inc(x_323);
lean_dec(x_298);
x_324 = l_Lean_IR_IRType_beq(x_323, x_292);
lean_dec(x_292);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_325 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_326 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_323);
x_327 = lean_unsigned_to_nat(120u);
x_328 = lean_unsigned_to_nat(0u);
x_329 = lean_format_pretty(x_326, x_327, x_328, x_328);
x_330 = lean_string_append(x_325, x_329);
lean_dec(x_329);
x_331 = lean_mk_string_unchecked("'", 1, 1);
x_332 = lean_string_append(x_330, x_331);
lean_dec(x_331);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_297, 0, x_333);
return x_297;
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_323);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_297, 0, x_335);
return x_297;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_336 = lean_ctor_get(x_297, 1);
lean_inc(x_336);
lean_dec(x_297);
x_337 = lean_ctor_get(x_298, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 x_338 = x_298;
} else {
 lean_dec_ref(x_298);
 x_338 = lean_box(0);
}
x_339 = l_Lean_IR_IRType_beq(x_337, x_292);
lean_dec(x_292);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_340 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_341 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_337);
x_342 = lean_unsigned_to_nat(120u);
x_343 = lean_unsigned_to_nat(0u);
x_344 = lean_format_pretty(x_341, x_342, x_343, x_343);
x_345 = lean_string_append(x_340, x_344);
lean_dec(x_344);
x_346 = lean_mk_string_unchecked("'", 1, 1);
x_347 = lean_string_append(x_345, x_346);
lean_dec(x_346);
if (lean_is_scalar(x_338)) {
 x_348 = lean_alloc_ctor(0, 1, 0);
} else {
 x_348 = x_338;
 lean_ctor_set_tag(x_348, 0);
}
lean_ctor_set(x_348, 0, x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_336);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_337);
x_350 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_351 = lean_alloc_ctor(1, 1, 0);
} else {
 x_351 = x_338;
}
lean_ctor_set(x_351, 0, x_350);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_336);
return x_352;
}
}
}
}
}
}
case 10:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_2, 0);
lean_inc(x_358);
lean_dec(x_2);
x_359 = l_Lean_IR_Checker_checkScalarType___redArg(x_1, x_4);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
if (lean_obj_tag(x_360) == 0)
{
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_3);
return x_359;
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = l_Lean_IR_Checker_checkObjVar(x_358, x_3, x_361);
lean_dec(x_3);
return x_362;
}
}
case 11:
{
lean_object* x_363; 
lean_dec(x_3);
x_363 = lean_ctor_get(x_2, 0);
lean_inc(x_363);
lean_dec(x_2);
if (lean_obj_tag(x_363) == 0)
{
uint8_t x_364; 
lean_dec(x_1);
x_364 = !lean_is_exclusive(x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_363, 0);
lean_dec(x_365);
x_366 = lean_box(0);
lean_ctor_set_tag(x_363, 1);
lean_ctor_set(x_363, 0, x_366);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_363);
lean_ctor_set(x_367, 1, x_4);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_363);
x_368 = lean_box(0);
x_369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_369, 0, x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_4);
return x_370;
}
}
else
{
lean_object* x_371; 
lean_dec(x_363);
x_371 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_4);
return x_371;
}
}
default: 
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_2, 0);
lean_inc(x_372);
lean_dec(x_2);
x_373 = l_Lean_IR_Checker_checkObjVar(x_372, x_3, x_4);
lean_dec(x_3);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 0)
{
lean_dec(x_374);
lean_dec(x_1);
return x_373;
}
else
{
uint8_t x_375; 
x_375 = !lean_is_exclusive(x_373);
if (x_375 == 0)
{
lean_object* x_376; uint8_t x_377; 
x_376 = lean_ctor_get(x_373, 0);
lean_dec(x_376);
x_377 = !lean_is_exclusive(x_374);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_378 = lean_ctor_get(x_374, 0);
lean_dec(x_378);
x_379 = lean_box(1);
x_380 = l_Lean_IR_IRType_beq(x_1, x_379);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_381 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_382 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_383 = lean_unsigned_to_nat(120u);
x_384 = lean_unsigned_to_nat(0u);
x_385 = lean_format_pretty(x_382, x_383, x_384, x_384);
x_386 = lean_string_append(x_381, x_385);
lean_dec(x_385);
x_387 = lean_mk_string_unchecked("'", 1, 1);
x_388 = lean_string_append(x_386, x_387);
lean_dec(x_387);
lean_ctor_set_tag(x_374, 0);
lean_ctor_set(x_374, 0, x_388);
return x_373;
}
else
{
lean_object* x_389; 
lean_dec(x_1);
x_389 = lean_box(0);
lean_ctor_set(x_374, 0, x_389);
return x_373;
}
}
else
{
lean_object* x_390; uint8_t x_391; 
lean_dec(x_374);
x_390 = lean_box(1);
x_391 = l_Lean_IR_IRType_beq(x_1, x_390);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_392 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_393 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_394 = lean_unsigned_to_nat(120u);
x_395 = lean_unsigned_to_nat(0u);
x_396 = lean_format_pretty(x_393, x_394, x_395, x_395);
x_397 = lean_string_append(x_392, x_396);
lean_dec(x_396);
x_398 = lean_mk_string_unchecked("'", 1, 1);
x_399 = lean_string_append(x_397, x_398);
lean_dec(x_398);
x_400 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_373, 0, x_400);
return x_373;
}
else
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_1);
x_401 = lean_box(0);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_373, 0, x_402);
return x_373;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_403 = lean_ctor_get(x_373, 1);
lean_inc(x_403);
lean_dec(x_373);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_404 = x_374;
} else {
 lean_dec_ref(x_374);
 x_404 = lean_box(0);
}
x_405 = lean_box(1);
x_406 = l_Lean_IR_IRType_beq(x_1, x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_407 = lean_mk_string_unchecked("unexpected type '", 17, 17);
x_408 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_409 = lean_unsigned_to_nat(120u);
x_410 = lean_unsigned_to_nat(0u);
x_411 = lean_format_pretty(x_408, x_409, x_410, x_410);
x_412 = lean_string_append(x_407, x_411);
lean_dec(x_411);
x_413 = lean_mk_string_unchecked("'", 1, 1);
x_414 = lean_string_append(x_412, x_413);
lean_dec(x_413);
if (lean_is_scalar(x_404)) {
 x_415 = lean_alloc_ctor(0, 1, 0);
} else {
 x_415 = x_404;
 lean_ctor_set_tag(x_415, 0);
}
lean_ctor_set(x_415, 0, x_414);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_403);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_1);
x_417 = lean_box(0);
if (lean_is_scalar(x_404)) {
 x_418 = lean_alloc_ctor(1, 1, 0);
} else {
 x_418 = x_404;
}
lean_ctor_set(x_418, 0, x_417);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_403);
return x_419;
}
}
}
}
}
block_9:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_7);
return x_8;
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Checker_checkExpr___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_7, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_apply_1(x_7, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_4, x_9, x_8);
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
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_4, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__4), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_5);
lean_closure_set(x_7, 6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__6___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_7);
x_9 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__8___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_5);
x_9 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_7);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__9), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_7);
x_9 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_1);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_apply_1(x_2, x_6);
lean_ctor_set(x_3, 0, x_7);
x_8 = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, lean_box(0));
lean_closure_set(x_12, 4, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__11), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, lean_box(0));
lean_closure_set(x_7, 4, lean_box(0));
lean_closure_set(x_7, 5, x_6);
lean_closure_set(x_7, 6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__12), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_ExceptT_bindCont), 7, 6);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, lean_box(0));
lean_closure_set(x_8, 4, lean_box(0));
lean_closure_set(x_8, 5, x_7);
x_9 = lean_alloc_closure((void*)(l_StateT_bind), 8, 7);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, lean_box(0));
lean_closure_set(x_9, 4, lean_box(0));
lean_closure_set(x_9, 5, x_5);
lean_closure_set(x_9, 6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_IR_Checker_markIndex___redArg(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_15 = x_7;
} else {
 lean_dec_ref(x_7);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_7, 0);
lean_dec(x_21);
x_22 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
lean_ctor_set(x_7, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_23 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
x_27 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_12 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0), 5, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__1), 5, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__2), 5, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__3), 5, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_19 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_20 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_21 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_22 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__5), 5, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_25);
x_27 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
lean_closure_set(x_27, 2, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
lean_inc(x_25);
x_29 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, lean_box(0));
lean_closure_set(x_29, 2, x_25);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_13);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_15);
lean_inc(x_25);
x_31 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, lean_box(0));
lean_closure_set(x_31, 2, x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_25);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__7), 6, 2);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_25);
lean_inc(x_32);
lean_inc(x_25);
x_34 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__10), 6, 2);
lean_closure_set(x_34, 0, x_25);
lean_closure_set(x_34, 1, x_32);
lean_inc(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__13), 6, 2);
lean_closure_set(x_35, 0, x_25);
lean_closure_set(x_35, 1, x_32);
lean_inc(x_32);
x_36 = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(x_36, 0, lean_box(0));
lean_closure_set(x_36, 1, lean_box(0));
lean_closure_set(x_36, 2, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
lean_inc(x_32);
x_38 = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(x_38, 0, lean_box(0));
lean_closure_set(x_38, 1, lean_box(0));
lean_closure_set(x_38, 2, x_32);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_33);
x_40 = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, lean_box(0));
lean_closure_set(x_40, 2, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_41);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get_size(x_1);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_1);
x_5 = x_43;
x_6 = x_4;
goto block_11;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_1);
x_5 = x_43;
x_6 = x_4;
goto block_11;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__14___boxed), 4, 0);
x_49 = lean_usize_of_nat(x_44);
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_42, x_48, x_1, x_49, x_50, x_43);
lean_inc(x_3);
x_52 = lean_apply_2(x_51, x_3, x_4);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
lean_dec(x_53);
x_5 = x_65;
x_6 = x_64;
goto block_11;
}
}
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_apply_2(x_2, x_9, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_withParams___lam__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_withParams___lam__8(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_withParams___lam__14(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_Checker_markIndex___redArg(x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_18 = x_10;
} else {
 lean_dec_ref(x_10);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = l_Lean_IR_LocalContext_addParam(x_4, x_7);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_22;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_5);
x_19 = l_Lean_IR_Checker_checkFnBody(x_18, x_5, x_6);
x_7 = x_19;
goto block_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_5);
x_21 = l_Lean_IR_Checker_checkFnBody(x_20, x_5, x_6);
x_7 = x_21;
goto block_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
block_15:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_14);
x_17 = l_Lean_IR_Checker_checkExpr(x_14, x_15, x_2, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
x_20 = l_Lean_IR_Checker_markIndex___redArg(x_13, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = l_Lean_IR_LocalContext_addLocal(x_24, x_13, x_14, x_15);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_1 = x_16;
x_2 = x_27;
x_3 = x_22;
goto _start;
}
}
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
lean_dec(x_1);
lean_inc(x_29);
x_46 = l_Lean_IR_Checker_markIndex___redArg(x_29, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_47);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_array_get_size(x_30);
x_52 = lean_nat_dec_lt(x_50, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
x_33 = x_49;
x_34 = x_48;
goto block_45;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_51, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
x_33 = x_49;
x_34 = x_48;
goto block_45;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_usize_of_nat(x_50);
x_55 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_56 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_30, x_54, x_55, x_49, x_48);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_56, 0, x_62);
return x_56;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_ctor_get(x_57, 0);
lean_inc(x_69);
lean_dec(x_57);
x_33 = x_69;
x_34 = x_68;
goto block_45;
}
}
}
}
block_45:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
lean_inc(x_36);
lean_inc(x_35);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_36);
lean_inc(x_31);
x_38 = l_Lean_IR_Checker_checkFnBody(x_31, x_37, x_34);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_IR_LocalContext_addJP(x_41, x_29, x_30, x_31);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_36);
x_1 = x_32;
x_2 = x_43;
x_3 = x_40;
goto _start;
}
}
}
case 2:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 3);
lean_inc(x_72);
lean_dec(x_1);
x_78 = l_Lean_IR_Checker_checkVar(x_70, x_2, x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_dec(x_79);
lean_dec(x_71);
x_73 = x_78;
goto block_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_IR_Checker_checkArg(x_71, x_2, x_80);
x_73 = x_81;
goto block_77;
}
block_77:
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_2);
return x_73;
}
else
{
lean_object* x_75; 
lean_dec(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_1 = x_72;
x_3 = x_75;
goto _start;
}
}
}
case 3:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 2);
lean_inc(x_83);
lean_dec(x_1);
x_84 = l_Lean_IR_Checker_checkVar(x_82, x_2, x_3);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_2);
return x_84;
}
else
{
lean_object* x_86; 
lean_dec(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_1 = x_83;
x_3 = x_86;
goto _start;
}
}
case 4:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 3);
lean_inc(x_90);
lean_dec(x_1);
x_96 = l_Lean_IR_Checker_checkVar(x_88, x_2, x_3);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_dec(x_97);
lean_dec(x_89);
x_91 = x_96;
goto block_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_IR_Checker_checkVar(x_89, x_2, x_98);
x_91 = x_99;
goto block_95;
}
block_95:
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_2);
return x_91;
}
else
{
lean_object* x_93; 
lean_dec(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_1 = x_90;
x_3 = x_93;
goto _start;
}
}
}
case 5:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_1, 5);
lean_inc(x_102);
lean_dec(x_1);
x_108 = l_Lean_IR_Checker_checkVar(x_100, x_2, x_3);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_dec(x_109);
lean_dec(x_101);
x_103 = x_108;
goto block_107;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_IR_Checker_checkVar(x_101, x_2, x_110);
x_103 = x_111;
goto block_107;
}
block_107:
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_2);
return x_103;
}
else
{
lean_object* x_105; 
lean_dec(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_1 = x_102;
x_3 = x_105;
goto _start;
}
}
}
case 8:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
lean_dec(x_1);
x_114 = l_Lean_IR_Checker_checkVar(x_112, x_2, x_3);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_2);
return x_114;
}
else
{
lean_object* x_116; 
lean_dec(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_1 = x_113;
x_3 = x_116;
goto _start;
}
}
case 9:
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
lean_dec(x_1);
x_1 = x_118;
goto _start;
}
case 10:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 3);
lean_inc(x_121);
lean_dec(x_1);
x_122 = l_Lean_IR_Checker_checkVar(x_120, x_2, x_3);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_2);
return x_122;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_122, 1);
x_126 = lean_ctor_get(x_122, 0);
lean_dec(x_126);
x_127 = !lean_is_exclusive(x_123);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_123, 0);
lean_dec(x_128);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_array_get_size(x_121);
x_131 = lean_box(0);
x_132 = lean_nat_dec_lt(x_129, x_130);
if (x_132 == 0)
{
lean_dec(x_130);
lean_dec(x_121);
lean_dec(x_2);
lean_ctor_set(x_123, 0, x_131);
return x_122;
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_130, x_130);
if (x_133 == 0)
{
lean_dec(x_130);
lean_dec(x_121);
lean_dec(x_2);
lean_ctor_set(x_123, 0, x_131);
return x_122;
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; 
lean_free_object(x_123);
lean_free_object(x_122);
x_134 = lean_usize_of_nat(x_129);
x_135 = lean_usize_of_nat(x_130);
lean_dec(x_130);
x_136 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_121, x_134, x_135, x_131, x_2, x_125);
lean_dec(x_121);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_123);
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_array_get_size(x_121);
x_139 = lean_box(0);
x_140 = lean_nat_dec_lt(x_137, x_138);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_121);
lean_dec(x_2);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_122, 0, x_141);
return x_122;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_138, x_138);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_138);
lean_dec(x_121);
lean_dec(x_2);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_122, 0, x_143);
return x_122;
}
else
{
size_t x_144; size_t x_145; lean_object* x_146; 
lean_free_object(x_122);
x_144 = lean_usize_of_nat(x_137);
x_145 = lean_usize_of_nat(x_138);
lean_dec(x_138);
x_146 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_121, x_144, x_145, x_139, x_2, x_125);
lean_dec(x_121);
return x_146;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_147 = lean_ctor_get(x_122, 1);
lean_inc(x_147);
lean_dec(x_122);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_148 = x_123;
} else {
 lean_dec_ref(x_123);
 x_148 = lean_box(0);
}
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_array_get_size(x_121);
x_151 = lean_box(0);
x_152 = lean_nat_dec_lt(x_149, x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_150);
lean_dec(x_121);
lean_dec(x_2);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_147);
return x_154;
}
else
{
uint8_t x_155; 
x_155 = lean_nat_dec_le(x_150, x_150);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_150);
lean_dec(x_121);
lean_dec(x_2);
if (lean_is_scalar(x_148)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_148;
}
lean_ctor_set(x_156, 0, x_151);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_147);
return x_157;
}
else
{
size_t x_158; size_t x_159; lean_object* x_160; 
lean_dec(x_148);
x_158 = lean_usize_of_nat(x_149);
x_159 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_160 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_121, x_158, x_159, x_151, x_2, x_147);
lean_dec(x_121);
return x_160;
}
}
}
}
}
case 11:
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
lean_dec(x_1);
x_162 = l_Lean_IR_Checker_checkArg(x_161, x_2, x_3);
lean_dec(x_2);
return x_162;
}
case 12:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_1, 1);
lean_inc(x_164);
lean_dec(x_1);
x_165 = l_Lean_IR_Checker_checkJP(x_163, x_2, x_3);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_2);
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_IR_Checker_checkArgs(x_164, x_2, x_167);
lean_dec(x_2);
lean_dec(x_164);
return x_168;
}
}
case 13:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_2);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_3);
return x_171;
}
default: 
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_1, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 2);
lean_inc(x_173);
lean_dec(x_1);
x_4 = x_172;
x_5 = x_173;
x_6 = x_2;
x_7 = x_3;
goto block_12;
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_Checker_checkVar(x_4, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_1 = x_5;
x_2 = x_6;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_4);
x_6 = x_13;
x_7 = x_3;
goto block_12;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_4);
x_6 = x_13;
x_7 = x_3;
goto block_12;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_usize_of_nat(x_14);
x_19 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_4, x_18, x_19, x_13, x_3);
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 1, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_6 = x_33;
x_7 = x_32;
goto block_12;
}
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Lean_IR_Checker_checkFnBody(x_5, x_10, x_7);
return x_11;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_box(0);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_get_size(x_34);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_2);
x_36 = x_3;
goto block_39;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_2);
x_36 = x_3;
goto block_39;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_usize_of_nat(x_40);
x_46 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_34, x_45, x_46, x_44, x_3);
lean_dec(x_34);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_47, 0, x_53);
return x_47;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_48);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_dec(x_47);
x_36 = x_59;
goto block_39;
}
}
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_IR_getEnv___redArg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_1);
lean_inc(x_2);
x_10 = l_Lean_IR_Checker_checkDecl(x_2, x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl___lam__0___boxed), 1, 0);
x_14 = lean_mk_string_unchecked("failed to compile definition, compiler IR check failed at '", 59, 59);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
x_15 = x_25;
goto block_24;
block_24:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
x_18 = l_Lean_Name_toString(x_15, x_17, x_13);
x_19 = lean_string_append(x_14, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked("'. Error: ", 10, 10);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_12);
lean_dec(x_12);
if (lean_is_scalar(x_7)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_7;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_2);
x_26 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_7;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_6);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_checkDecl___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = l_Lean_IR_checkDecl___redArg(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_usize_of_nat(x_4);
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
lean_inc(x_1);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___redArg(x_1, x_1, x_11, x_12, x_6, x_3);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Checker_maxCtorFields = _init_l_Lean_IR_Checker_maxCtorFields();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields);
l_Lean_IR_Checker_maxCtorScalarsSize = _init_l_Lean_IR_Checker_maxCtorScalarsSize();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize);
l_Lean_IR_Checker_maxCtorTag = _init_l_Lean_IR_Checker_maxCtorTag();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorTag);
l_Lean_IR_Checker_usizeSize = _init_l_Lean_IR_Checker_usizeSize();
lean_mark_persistent(l_Lean_IR_Checker_usizeSize);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
