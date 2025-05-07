// Lean compiler output
// Module: Lean.Compiler.IR.RC
// Imports: Lean.Runtime Lean.Compiler.IR.CompilerM Lean.Compiler.IR.LiveVars
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_erase___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_bindVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitFnBody(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_IR_LiveVars_collectExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_processVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_instInhabitedVarInfo;
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkLiveVarSet(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxSmallNat;
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitRC_mustConsume(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr___boxed(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LiveVars_updateJPLiveVarMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_mustConsume___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
lean_object* l_Lean_IR_LiveVars_collectFnBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_collectJP_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getVarInfo_spec__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ExplicitRC_instInhabitedVarInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_findEnvDecl_x27(x_3, x_2, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_mk_string_unchecked("Lean.Compiler.IR.RC", 19, 19);
x_7 = lean_mk_string_unchecked("Lean.IR.ExplicitRC.getDecl", 26, 26);
x_8 = lean_unsigned_to_nat(36u);
x_9 = lean_unsigned_to_nat(17u);
x_10 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_11 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_12 = l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getVarInfo_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitRC_instInhabitedVarInfo;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_mk_string_unchecked("Lean.Compiler.IR.RC", 19, 19);
x_6 = lean_mk_string_unchecked("Lean.IR.ExplicitRC.getVarInfo", 29, 29);
x_7 = lean_unsigned_to_nat(41u);
x_8 = lean_unsigned_to_nat(17u);
x_9 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_IR_ExplicitRC_getVarInfo_spec__1(x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = l_Lean_IR_LocalContext_getJPParams(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_mk_string_unchecked("Lean.Compiler.IR.RC", 19, 19);
x_6 = lean_mk_string_unchecked("Lean.IR.ExplicitRC.getJPParams", 30, 30);
x_7 = lean_unsigned_to_nat(46u);
x_8 = lean_unsigned_to_nat(15u);
x_9 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0(x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getJPParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_RBNode_find___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_collectJP_spec__0___redArg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getJPLiveVars(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitRC_mustConsume(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_4 = lean_ctor_get_uint8(x_3, 0);
if (x_4 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_3, 2);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_mustConsume___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExplicitRC_mustConsume(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_8 = lean_box(1);
x_9 = lean_ctor_get_uint8(x_7, 1);
lean_dec(x_7);
x_10 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_3);
x_11 = lean_unbox(x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_9);
return x_10;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitRC_addInc(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_box(1);
x_7 = lean_ctor_get_uint8(x_4, 1);
lean_dec(x_4);
x_8 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_3);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitRC_addDec(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_CtorInfo_isRef(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_13 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_5, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_2);
x_8 = x_5;
goto block_12;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, 1);
x_16 = lean_ctor_get_uint8(x_14, 2);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_17, 0, x_4);
lean_ctor_set_uint8(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, 2, x_16);
x_18 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_5, x_2, x_17);
x_8 = x_18;
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_9);
lean_ctor_set(x_11, 4, x_10);
return x_11;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_1, x_2, x_3, x_5);
x_9 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_1, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = l_Lean_IR_ExplicitRC_mustConsume(x_2, x_6);
if (x_10 == 0)
{
x_3 = x_8;
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_6);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_ctor_get_uint8(x_12, 1);
lean_dec(x_12);
lean_inc(x_6);
x_15 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_14);
x_3 = x_15;
x_4 = x_7;
goto _start;
}
}
else
{
lean_dec(x_9);
x_3 = x_8;
x_4 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_3, x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_IR_instInhabitedArg;
x_8 = lean_array_get(x_7, x_1, x_2);
x_9 = lean_nat_sub(x_3, x_4);
x_10 = lean_array_get(x_7, x_1, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_Arg_beq(x_10, x_8);
lean_dec(x_8);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_4);
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
x_3 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_1, x_2, x_2, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 1)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
x_15 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_16 = lean_array_fget(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_15);
x_12 = x_18;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_3);
x_19 = lean_apply_1(x_3, x_15);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_12 = x_18;
goto block_14;
}
else
{
x_5 = x_11;
goto _start;
}
}
}
else
{
lean_dec(x_15);
x_5 = x_11;
goto _start;
}
block_14:
{
if (x_12 == 0)
{
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_3);
return x_12;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(x_2, x_1, x_3, x_4, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get(x_1, x_2, x_3);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_IR_instInhabitedParam;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 1)
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
x_16 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_17 = lean_array_fget(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_nat_dec_eq(x_2, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_16);
x_11 = x_19;
goto block_15;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_3);
x_20 = lean_apply_1(x_3, x_16);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_11 = x_21;
goto block_15;
}
}
else
{
lean_dec(x_16);
x_5 = x_10;
goto _start;
}
block_15:
{
if (x_11 == 0)
{
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_nat_add(x_6, x_9);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_6 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(x_2, x_1, x_3, x_4, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 1)
{
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_array_fget(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_14);
x_16 = lean_ctor_get_uint8(x_15, 0);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_18; lean_object* x_19; 
lean_inc(x_12);
x_18 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_1, x_12, x_12, x_12);
lean_dec(x_12);
if (x_18 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_35; 
lean_inc(x_3);
x_27 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(x_14, x_1, x_3);
x_35 = lean_ctor_get_uint8(x_15, 2);
if (x_35 == 0)
{
if (x_18 == 0)
{
goto block_34;
}
else
{
x_28 = x_18;
goto block_30;
}
}
else
{
goto block_34;
}
block_30:
{
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_nat_sub(x_27, x_10);
lean_dec(x_27);
x_19 = x_29;
goto block_25;
}
else
{
x_19 = x_27;
goto block_25;
}
}
block_32:
{
uint8_t x_31; 
lean_inc(x_3);
x_31 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(x_14, x_1, x_3);
x_28 = x_31;
goto block_30;
}
block_34:
{
lean_object* x_33; 
x_33 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_4, x_14);
if (lean_obj_tag(x_33) == 0)
{
goto block_32;
}
else
{
lean_dec(x_33);
if (x_18 == 0)
{
goto block_32;
}
else
{
x_28 = x_18;
goto block_30;
}
}
}
}
block_25:
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_19, x_8);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_ctor_get_uint8(x_15, 1);
lean_dec(x_15);
x_22 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_7);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_21);
x_6 = x_11;
x_7 = x_22;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
}
}
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(x_2, x_1, x_3, x_5, x_6, x_6, x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_instInhabitedParam;
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_3);
x_8 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 1)
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_array_fget(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_26 = l_Lean_IR_ExplicitRC_mustConsume(x_4, x_14);
if (x_26 == 0)
{
lean_dec(x_12);
x_15 = x_26;
goto block_25;
}
else
{
uint8_t x_27; 
lean_inc(x_12);
x_27 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_1, x_12, x_12, x_12);
lean_dec(x_12);
x_15 = x_27;
goto block_25;
}
block_25:
{
if (x_15 == 0)
{
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_17; 
lean_inc(x_2);
x_17 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(x_14, x_1, x_2);
if (x_17 == 0)
{
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_3, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = l_Lean_IR_ExplicitRC_getVarInfo(x_4, x_14);
x_21 = lean_ctor_get_uint8(x_20, 1);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_7);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_21);
x_6 = x_11;
x_7 = x_22;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
}
}
}
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(x_2, x_3, x_5, x_1, x_6, x_6, x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0___boxed), 1, 0);
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_3, x_4);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = l_Lean_IR_IRType_isObj(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_14);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_ctor_get_uint8(x_20, 1);
lean_dec(x_20);
x_23 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_6);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_22);
x_7 = x_23;
goto block_12;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
x_7 = x_6;
goto block_12;
}
}
}
else
{
lean_dec(x_14);
x_7 = x_6;
goto block_12;
}
}
else
{
return x_6;
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_5);
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(x_4, x_1, x_2, x_9, x_10, x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Array_isEmpty___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 2);
lean_dec(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
x_3 = x_10;
goto block_7;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_nat_dec_eq(x_11, x_9);
x_3 = x_12;
goto block_7;
}
block_7:
{
if (x_3 == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
return x_6;
}
}
}
case 11:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = l_Lean_maxSmallNat;
x_16 = lean_nat_dec_le(x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_17; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_17 = l_Lean_IR_IRType_isObj(x_3);
if (x_17 == 0)
{
x_8 = x_17;
goto block_16;
}
else
{
uint8_t x_18; 
x_18 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(x_4);
if (x_18 == 0)
{
x_8 = x_17;
goto block_16;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_8 = x_20;
goto block_16;
}
}
block_16:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(x_4);
x_10 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(x_7, x_4);
x_11 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_11, 0, x_8);
lean_ctor_set_uint8(x_11, 1, x_9);
lean_ctor_set_uint8(x_11, 2, x_10);
x_12 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_7, x_2, x_11);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_15, 4, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_11; 
x_11 = l_Lean_IR_ExplicitRC_mustConsume(x_1, x_2);
if (x_11 == 0)
{
x_5 = x_11;
goto block_10;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_4, x_2);
if (lean_obj_tag(x_12) == 0)
{
x_5 = x_11;
goto block_10;
}
else
{
lean_dec(x_12);
lean_dec(x_2);
return x_3;
}
}
block_10:
{
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_ctor_get_uint8(x_6, 1);
lean_dec(x_6);
x_9 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_processVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_4);
lean_ctor_set(x_13, 3, x_5);
x_14 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_12, x_13, x_6);
lean_dec(x_12);
lean_dec(x_1);
x_7 = x_14;
goto block_11;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_5);
x_17 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_15, x_16, x_6);
lean_dec(x_15);
lean_dec(x_1);
x_7 = x_17;
goto block_11;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_18);
x_19 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_18, x_5, x_6);
x_20 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_18);
lean_dec(x_18);
x_21 = lean_ctor_get_uint8(x_20, 2);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_19);
x_7 = x_22;
goto block_11;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
lean_dec(x_1);
x_25 = lean_ctor_get_uint8(x_24, 1);
lean_dec(x_24);
lean_inc(x_2);
x_26 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_25);
lean_inc(x_4);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_26);
x_7 = x_27;
goto block_11;
}
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
x_29 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_28, x_5, x_6);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_4);
lean_ctor_set(x_30, 3, x_29);
x_7 = x_30;
goto block_11;
}
case 5:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 2);
lean_inc(x_31);
x_32 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_31, x_5, x_6);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_32);
x_7 = x_33;
goto block_11;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_1);
x_41 = l_Lean_IR_ExplicitRC_getDecl(x_1, x_34);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_36 = x_42;
goto block_40;
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_36);
x_37 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(x_1, x_35, x_36, x_5, x_6);
lean_inc(x_4);
lean_inc(x_2);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_37);
x_39 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(x_1, x_35, x_36, x_38, x_6);
lean_dec(x_35);
lean_dec(x_1);
x_7 = x_39;
goto block_11;
}
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_4);
lean_inc(x_2);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_5);
x_45 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_43, x_44, x_6);
lean_dec(x_43);
lean_dec(x_1);
x_7 = x_45;
goto block_11;
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_array_push(x_47, x_48);
lean_inc(x_4);
lean_inc(x_2);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_3);
lean_ctor_set(x_50, 2, x_4);
lean_ctor_set(x_50, 3, x_5);
x_51 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_49, x_50, x_6);
lean_dec(x_49);
lean_dec(x_1);
x_7 = x_51;
goto block_11;
}
case 10:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
x_53 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_52, x_5, x_6);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_3);
lean_ctor_set(x_54, 2, x_4);
lean_ctor_set(x_54, 3, x_53);
x_7 = x_54;
goto block_11;
}
default: 
{
lean_object* x_55; 
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set(x_55, 3, x_5);
x_7 = x_55;
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_IR_LiveVars_collectExpr(x_4, x_6);
x_9 = l_Lean_RBNode_erase___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_bindVar_spec__0___redArg(x_2, x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_18; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Lean_IR_IRType_isObj(x_8);
lean_dec(x_8);
x_18 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
lean_dec(x_6);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_10 = x_20;
goto block_17;
}
else
{
x_10 = x_5;
goto block_17;
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_11 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, 1, x_5);
lean_ctor_set_uint8(x_11, 2, x_10);
x_12 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_4, x_7, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
x_3 = x_10;
goto block_9;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_12, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
x_3 = x_10;
goto block_9;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_11);
x_16 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(x_2, x_15, x_16, x_10);
x_3 = x_17;
goto block_9;
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_box(0);
lean_inc(x_3);
x_10 = l_Lean_IR_LiveVars_collectFnBody(x_3, x_8, x_9);
x_11 = lean_array_uget(x_6, x_5);
x_12 = lean_box(0);
x_13 = lean_array_uset(x_6, x_5, x_12);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(x_1, x_2, x_22);
lean_inc(x_24);
x_25 = l_Lean_IR_ExplicitRC_visitFnBody(x_23, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_27, x_24, x_26, x_10);
lean_dec(x_10);
lean_dec(x_24);
lean_dec(x_27);
lean_ctor_set(x_11, 1, x_28);
x_14 = x_11;
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(x_1, x_2, x_29);
lean_inc(x_31);
x_32 = l_Lean_IR_ExplicitRC_visitFnBody(x_30, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_34, x_31, x_33, x_10);
lean_dec(x_10);
lean_dec(x_31);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
x_14 = x_36;
goto block_20;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_1);
x_39 = l_Lean_IR_ExplicitRC_visitFnBody(x_38, x_1);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_41, x_1, x_40, x_10);
lean_dec(x_10);
lean_dec(x_41);
lean_ctor_set(x_11, 0, x_42);
x_14 = x_11;
goto block_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
lean_dec(x_11);
lean_inc(x_1);
x_44 = l_Lean_IR_ExplicitRC_visitFnBody(x_43, x_1);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_46, x_1, x_45, x_10);
lean_dec(x_10);
lean_dec(x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_14 = x_48;
goto block_20;
}
}
block_20:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_5, x_16);
x_18 = lean_array_uset(x_13, x_5, x_14);
x_5 = x_17;
x_6 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_3);
x_7 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(x_2, x_3, x_4, x_5);
lean_inc(x_7);
x_8 = l_Lean_IR_ExplicitRC_visitFnBody(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_processVDecl(x_7, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_17 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_2, x_14);
lean_inc(x_17);
x_18 = l_Lean_IR_ExplicitRC_visitFnBody(x_15, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_17, x_14, x_19, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_21);
lean_inc(x_13);
x_26 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_13, x_14, x_21, x_25);
x_27 = lean_ctor_get(x_2, 4);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_21);
lean_inc(x_14);
lean_inc(x_13);
x_28 = l_Lean_IR_LocalContext_addJP(x_27, x_13, x_14, x_21);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_28);
x_30 = l_Lean_IR_ExplicitRC_visitFnBody(x_16, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_1, 3, x_32);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_1, 3, x_33);
lean_ctor_set(x_1, 2, x_21);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 2);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
lean_inc(x_2);
x_40 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_2, x_37);
lean_inc(x_40);
x_41 = l_Lean_IR_ExplicitRC_visitFnBody(x_38, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_40, x_37, x_42, x_43);
lean_dec(x_43);
lean_dec(x_40);
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 3);
lean_inc(x_48);
lean_inc(x_44);
lean_inc(x_36);
x_49 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_36, x_37, x_44, x_48);
x_50 = lean_ctor_get(x_2, 4);
lean_inc(x_50);
lean_dec(x_2);
lean_inc(x_44);
lean_inc(x_37);
lean_inc(x_36);
x_51 = l_Lean_IR_LocalContext_addJP(x_50, x_36, x_37, x_44);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_51);
x_53 = l_Lean_IR_ExplicitRC_visitFnBody(x_39, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_57, 0, x_36);
lean_ctor_set(x_57, 1, x_37);
lean_ctor_set(x_57, 2, x_44);
lean_ctor_set(x_57, 3, x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
case 4:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_1);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_1, 0);
x_61 = lean_ctor_get(x_1, 3);
x_62 = l_Lean_IR_ExplicitRC_visitFnBody(x_61, x_2);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = lean_box(0);
lean_inc(x_60);
x_67 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_65, x_60, x_66);
lean_ctor_set(x_1, 3, x_64);
lean_ctor_set(x_62, 1, x_67);
lean_ctor_set(x_62, 0, x_1);
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_box(0);
lean_inc(x_60);
x_71 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_69, x_60, x_70);
lean_ctor_set(x_1, 3, x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_ctor_get(x_1, 1);
x_75 = lean_ctor_get(x_1, 2);
x_76 = lean_ctor_get(x_1, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_1);
x_77 = l_Lean_IR_ExplicitRC_visitFnBody(x_76, x_2);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
lean_inc(x_73);
x_82 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_79, x_73, x_81);
x_83 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_83, 2, x_75);
lean_ctor_set(x_83, 3, x_78);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
case 5:
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_1);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_1, 0);
x_87 = lean_ctor_get(x_1, 5);
x_88 = l_Lean_IR_ExplicitRC_visitFnBody(x_87, x_2);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
x_92 = lean_box(0);
lean_inc(x_86);
x_93 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_91, x_86, x_92);
lean_ctor_set(x_1, 5, x_90);
lean_ctor_set(x_88, 1, x_93);
lean_ctor_set(x_88, 0, x_1);
return x_88;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_88, 0);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_88);
x_96 = lean_box(0);
lean_inc(x_86);
x_97 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_95, x_86, x_96);
lean_ctor_set(x_1, 5, x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_1, 0);
x_100 = lean_ctor_get(x_1, 1);
x_101 = lean_ctor_get(x_1, 2);
x_102 = lean_ctor_get(x_1, 3);
x_103 = lean_ctor_get(x_1, 4);
x_104 = lean_ctor_get(x_1, 5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_1);
x_105 = l_Lean_IR_ExplicitRC_visitFnBody(x_104, x_2);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
lean_inc(x_99);
x_110 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_107, x_99, x_109);
x_111 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_100);
lean_ctor_set(x_111, 2, x_101);
lean_ctor_set(x_111, 3, x_102);
lean_ctor_set(x_111, 4, x_103);
lean_ctor_set(x_111, 5, x_106);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
case 9:
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_1);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_1, 1);
x_115 = l_Lean_IR_ExplicitRC_visitFnBody(x_114, x_2);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_ctor_set(x_1, 1, x_117);
lean_ctor_set(x_115, 0, x_1);
return x_115;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_115, 0);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_115);
lean_ctor_set(x_1, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_1, 0);
x_122 = lean_ctor_get(x_1, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_1);
x_123 = l_Lean_IR_ExplicitRC_visitFnBody(x_122, x_2);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_121);
lean_ctor_set(x_127, 1, x_124);
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
case 10:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; size_t x_136; lean_object* x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_1, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_1, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_2, 3);
lean_inc(x_133);
x_134 = lean_box(0);
lean_inc(x_1);
x_135 = l_Lean_IR_LiveVars_collectFnBody(x_1, x_133, x_134);
x_136 = lean_array_size(x_132);
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_usize_of_nat(x_137);
lean_inc(x_1);
lean_inc(x_130);
x_139 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(x_2, x_130, x_1, x_136, x_138, x_132);
x_140 = !lean_is_exclusive(x_1);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_1, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_1, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_1, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_1, 0);
lean_dec(x_144);
lean_ctor_set(x_1, 3, x_139);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_1);
lean_ctor_set(x_145, 1, x_135);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_1);
x_146 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_146, 0, x_129);
lean_ctor_set(x_146, 1, x_130);
lean_ctor_set(x_146, 2, x_131);
lean_ctor_set(x_146, 3, x_139);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_135);
return x_147;
}
}
case 11:
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_1, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_153; lean_object* x_161; uint8_t x_162; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_161 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_149);
x_162 = lean_ctor_get_uint8(x_161, 0);
if (x_162 == 0)
{
lean_dec(x_161);
x_153 = x_162;
goto block_160;
}
else
{
uint8_t x_163; 
x_163 = lean_ctor_get_uint8(x_161, 2);
lean_dec(x_161);
if (x_163 == 0)
{
x_153 = x_162;
goto block_160;
}
else
{
lean_dec(x_2);
goto block_152;
}
}
block_152:
{
lean_object* x_150; lean_object* x_151; 
x_150 = l_Lean_IR_mkLiveVarSet(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_1);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
block_160:
{
if (x_153 == 0)
{
lean_dec(x_2);
goto block_152;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_unsigned_to_nat(1u);
x_155 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_149);
lean_dec(x_2);
x_156 = lean_ctor_get_uint8(x_155, 1);
lean_dec(x_155);
lean_inc(x_149);
x_157 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_157, 0, x_149);
lean_ctor_set(x_157, 1, x_154);
lean_ctor_set(x_157, 2, x_1);
lean_ctor_set_uint8(x_157, sizeof(void*)*3, x_153);
lean_ctor_set_uint8(x_157, sizeof(void*)*3 + 1, x_156);
x_158 = l_Lean_IR_mkLiveVarSet(x_149);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_2);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
case 12:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_1, 1);
lean_inc(x_167);
x_168 = l_Lean_IR_ExplicitRC_getJPLiveVars(x_2, x_166);
x_169 = l_Lean_IR_ExplicitRC_getJPParams(x_2, x_166);
lean_dec(x_166);
x_170 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(x_2, x_167, x_169, x_1, x_168);
lean_dec(x_168);
lean_dec(x_167);
x_171 = lean_ctor_get(x_2, 3);
lean_inc(x_171);
lean_dec(x_2);
x_172 = lean_box(0);
lean_inc(x_170);
x_173 = l_Lean_IR_LiveVars_collectFnBody(x_170, x_171, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_170);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
case 13:
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_2);
x_175 = lean_box(0);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_1);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
default: 
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_2);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 4, x_6);
x_8 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_7, x_4);
lean_inc(x_8);
x_9 = l_Lean_IR_ExplicitRC_visitFnBody(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_8, x_4, x_10, x_11);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_8);
x_13 = l_Lean_IR_Decl_updateBody_x21(x_3, x_12);
return x_13;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_getEnv___redArg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitRC_visitDecl), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_array_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(x_6, x_7, x_9, x_1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitRC_visitDecl), 3, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
x_14 = lean_array_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_usize_of_nat(x_15);
x_17 = l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(x_13, x_14, x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitRC___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitRC(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_LiveVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_RC(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Runtime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LiveVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExplicitRC_instInhabitedVarInfo = _init_l_Lean_IR_ExplicitRC_instInhabitedVarInfo();
lean_mark_persistent(l_Lean_IR_ExplicitRC_instInhabitedVarInfo);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
