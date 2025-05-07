// Lean compiler output
// Module: Lean.Compiler.IR.ExpandResetReuse
// Imports: Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds Lean.Compiler.IR.FreeVars
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_IR_push(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instBEqVarId;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
lean_object* l_Lean_IR_instHashableVarId___lam__0___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4___lam__0(lean_object*);
lean_object* l_Array_back_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_computeProjCounts(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_computeProjCounts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_instBEqVarId;
x_5 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
switch (lean_obj_tag(x_2)) {
case 3:
{
goto block_78;
}
case 4:
{
goto block_78;
}
case 5:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_3);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; lean_object* x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; size_t x_92; size_t x_93; lean_object* x_94; size_t x_95; size_t x_96; size_t x_97; lean_object* x_98; uint8_t x_99; 
x_80 = lean_ctor_get(x_3, 0);
x_81 = lean_ctor_get(x_3, 1);
x_82 = lean_array_get_size(x_81);
x_83 = lean_uint64_of_nat(x_1);
x_84 = lean_unsigned_to_nat(32u);
x_85 = lean_uint64_of_nat(x_84);
x_86 = lean_uint64_shift_right(x_83, x_85);
x_87 = lean_uint64_xor(x_83, x_86);
x_88 = lean_unsigned_to_nat(16u);
x_89 = lean_uint64_of_nat(x_88);
x_90 = lean_uint64_shift_right(x_87, x_89);
x_91 = lean_uint64_xor(x_87, x_90);
x_92 = lean_uint64_to_usize(x_91);
x_93 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_usize_of_nat(x_94);
x_96 = lean_usize_sub(x_93, x_95);
x_97 = lean_usize_land(x_92, x_96);
x_98 = lean_array_uget(x_81, x_97);
lean_inc(x_98);
lean_inc(x_1);
x_99 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_4, x_1, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_100 = lean_nat_add(x_80, x_94);
lean_dec(x_80);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_2);
lean_ctor_set(x_101, 2, x_98);
x_102 = lean_array_uset(x_81, x_97, x_101);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_shiftl(x_100, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_le(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_102);
lean_ctor_set(x_3, 1, x_109);
lean_ctor_set(x_3, 0, x_100);
return x_3;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_102);
lean_ctor_set(x_3, 0, x_100);
return x_3;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_5);
x_110 = lean_box(0);
x_111 = lean_array_uset(x_81, x_97, x_110);
x_112 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_98);
x_113 = lean_array_uset(x_111, x_97, x_112);
lean_ctor_set(x_3, 1, x_113);
return x_3;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; lean_object* x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; size_t x_126; size_t x_127; lean_object* x_128; size_t x_129; size_t x_130; size_t x_131; lean_object* x_132; uint8_t x_133; 
x_114 = lean_ctor_get(x_3, 0);
x_115 = lean_ctor_get(x_3, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_3);
x_116 = lean_array_get_size(x_115);
x_117 = lean_uint64_of_nat(x_1);
x_118 = lean_unsigned_to_nat(32u);
x_119 = lean_uint64_of_nat(x_118);
x_120 = lean_uint64_shift_right(x_117, x_119);
x_121 = lean_uint64_xor(x_117, x_120);
x_122 = lean_unsigned_to_nat(16u);
x_123 = lean_uint64_of_nat(x_122);
x_124 = lean_uint64_shift_right(x_121, x_123);
x_125 = lean_uint64_xor(x_121, x_124);
x_126 = lean_uint64_to_usize(x_125);
x_127 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_usize_of_nat(x_128);
x_130 = lean_usize_sub(x_127, x_129);
x_131 = lean_usize_land(x_126, x_130);
x_132 = lean_array_uget(x_115, x_131);
lean_inc(x_132);
lean_inc(x_1);
x_133 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_4, x_1, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_134 = lean_nat_add(x_114, x_128);
lean_dec(x_114);
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_2);
lean_ctor_set(x_135, 2, x_132);
x_136 = lean_array_uset(x_115, x_131, x_135);
x_137 = lean_unsigned_to_nat(2u);
x_138 = lean_nat_shiftl(x_134, x_137);
x_139 = lean_unsigned_to_nat(3u);
x_140 = lean_nat_div(x_138, x_139);
lean_dec(x_138);
x_141 = lean_array_get_size(x_136);
x_142 = lean_nat_dec_le(x_140, x_141);
lean_dec(x_141);
lean_dec(x_140);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_136);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
else
{
lean_object* x_145; 
lean_dec(x_5);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_134);
lean_ctor_set(x_145, 1, x_136);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_5);
x_146 = lean_box(0);
x_147 = lean_array_uset(x_115, x_131, x_146);
x_148 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_132);
x_149 = lean_array_uset(x_147, x_131, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_114);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
default: 
{
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
block_78:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_uint64_of_nat(x_1);
x_11 = lean_unsigned_to_nat(32u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_sub(x_20, x_22);
x_24 = lean_usize_land(x_19, x_23);
x_25 = lean_array_uget(x_8, x_24);
lean_inc(x_25);
lean_inc(x_1);
x_26 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_4, x_1, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_25);
x_29 = lean_array_uset(x_8, x_24, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_shiftl(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_29);
lean_ctor_set(x_3, 1, x_36);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_29);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
x_37 = lean_box(0);
x_38 = lean_array_uset(x_8, x_24, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_25);
x_40 = lean_array_uset(x_38, x_24, x_39);
lean_ctor_set(x_3, 1, x_40);
return x_3;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; lean_object* x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_41 = lean_ctor_get(x_3, 0);
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_3);
x_43 = lean_array_get_size(x_42);
x_44 = lean_uint64_of_nat(x_1);
x_45 = lean_unsigned_to_nat(32u);
x_46 = lean_uint64_of_nat(x_45);
x_47 = lean_uint64_shift_right(x_44, x_46);
x_48 = lean_uint64_xor(x_44, x_47);
x_49 = lean_unsigned_to_nat(16u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_right(x_48, x_50);
x_52 = lean_uint64_xor(x_48, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_usize_of_nat(x_55);
x_57 = lean_usize_sub(x_54, x_56);
x_58 = lean_usize_land(x_53, x_57);
x_59 = lean_array_uget(x_42, x_58);
lean_inc(x_59);
lean_inc(x_1);
x_60 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_4, x_1, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_61 = lean_nat_add(x_41, x_55);
lean_dec(x_41);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
lean_ctor_set(x_62, 2, x_59);
x_63 = lean_array_uset(x_42, x_58, x_62);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_nat_shiftl(x_61, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_5, x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_5);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_63);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_5);
x_73 = lean_box(0);
x_74 = lean_array_uset(x_42, x_58, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_4, x_1, x_2, x_59);
x_76 = lean_array_uset(x_74, x_58, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_41);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = lean_unsigned_to_nat(32u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = lean_unsigned_to_nat(16u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_sub(x_17, x_19);
x_21 = lean_usize_land(x_16, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_uint64_of_nat(x_25);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_1, x_2, x_7);
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
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_13, x_4);
x_5 = x_14;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_15, x_4);
x_5 = x_16;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
switch (lean_obj_tag(x_4)) {
case 3:
{
goto block_79;
}
case 4:
{
goto block_79;
}
case 5:
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_5, x_2);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint64_t x_85; lean_object* x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; lean_object* x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; size_t x_94; size_t x_95; lean_object* x_96; size_t x_97; size_t x_98; size_t x_99; lean_object* x_100; uint8_t x_101; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_array_get_size(x_83);
x_85 = lean_uint64_of_nat(x_3);
x_86 = lean_unsigned_to_nat(32u);
x_87 = lean_uint64_of_nat(x_86);
x_88 = lean_uint64_shift_right(x_85, x_87);
x_89 = lean_uint64_xor(x_85, x_88);
x_90 = lean_unsigned_to_nat(16u);
x_91 = lean_uint64_of_nat(x_90);
x_92 = lean_uint64_shift_right(x_89, x_91);
x_93 = lean_uint64_xor(x_89, x_92);
x_94 = lean_uint64_to_usize(x_93);
x_95 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_usize_of_nat(x_96);
x_98 = lean_usize_sub(x_95, x_97);
x_99 = lean_usize_land(x_94, x_98);
x_100 = lean_array_uget(x_83, x_99);
x_101 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_102 = lean_nat_add(x_82, x_96);
lean_dec(x_82);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_3);
lean_ctor_set(x_103, 1, x_4);
lean_ctor_set(x_103, 2, x_100);
x_104 = lean_array_uset(x_83, x_99, x_103);
x_105 = lean_unsigned_to_nat(2u);
x_106 = lean_nat_shiftl(x_102, x_105);
x_107 = lean_unsigned_to_nat(3u);
x_108 = lean_nat_div(x_106, x_107);
lean_dec(x_106);
x_109 = lean_array_get_size(x_104);
x_110 = lean_nat_dec_le(x_108, x_109);
lean_dec(x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_104);
lean_ctor_set(x_80, 1, x_111);
lean_ctor_set(x_80, 0, x_102);
return x_80;
}
else
{
lean_ctor_set(x_80, 1, x_104);
lean_ctor_set(x_80, 0, x_102);
return x_80;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_box(0);
x_113 = lean_array_uset(x_83, x_99, x_112);
x_114 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_100);
x_115 = lean_array_uset(x_113, x_99, x_114);
lean_ctor_set(x_80, 1, x_115);
return x_80;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint64_t x_119; lean_object* x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; lean_object* x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; size_t x_128; size_t x_129; lean_object* x_130; size_t x_131; size_t x_132; size_t x_133; lean_object* x_134; uint8_t x_135; 
x_116 = lean_ctor_get(x_80, 0);
x_117 = lean_ctor_get(x_80, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_80);
x_118 = lean_array_get_size(x_117);
x_119 = lean_uint64_of_nat(x_3);
x_120 = lean_unsigned_to_nat(32u);
x_121 = lean_uint64_of_nat(x_120);
x_122 = lean_uint64_shift_right(x_119, x_121);
x_123 = lean_uint64_xor(x_119, x_122);
x_124 = lean_unsigned_to_nat(16u);
x_125 = lean_uint64_of_nat(x_124);
x_126 = lean_uint64_shift_right(x_123, x_125);
x_127 = lean_uint64_xor(x_123, x_126);
x_128 = lean_uint64_to_usize(x_127);
x_129 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_usize_of_nat(x_130);
x_132 = lean_usize_sub(x_129, x_131);
x_133 = lean_usize_land(x_128, x_132);
x_134 = lean_array_uget(x_117, x_133);
x_135 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_136 = lean_nat_add(x_116, x_130);
lean_dec(x_116);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_3);
lean_ctor_set(x_137, 1, x_4);
lean_ctor_set(x_137, 2, x_134);
x_138 = lean_array_uset(x_117, x_133, x_137);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_shiftl(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_138);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_138);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_box(0);
x_149 = lean_array_uset(x_117, x_133, x_148);
x_150 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_134);
x_151 = lean_array_uset(x_149, x_133, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_116);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
x_1 = x_5;
goto _start;
}
}
block_79:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_uint64_of_nat(x_3);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_9, x_25);
x_27 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 2, x_26);
x_30 = lean_array_uset(x_9, x_25, x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_shiftl(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_30);
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
else
{
lean_ctor_set(x_6, 1, x_30);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_uset(x_9, x_25, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_26);
x_41 = lean_array_uset(x_39, x_25, x_40);
lean_ctor_set(x_6, 1, x_41);
return x_6;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; size_t x_54; size_t x_55; lean_object* x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_array_get_size(x_43);
x_45 = lean_uint64_of_nat(x_3);
x_46 = lean_unsigned_to_nat(32u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_xor(x_45, x_48);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_uint64_of_nat(x_50);
x_52 = lean_uint64_shift_right(x_49, x_51);
x_53 = lean_uint64_xor(x_49, x_52);
x_54 = lean_uint64_to_usize(x_53);
x_55 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_usize_of_nat(x_56);
x_58 = lean_usize_sub(x_55, x_57);
x_59 = lean_usize_land(x_54, x_58);
x_60 = lean_array_uget(x_43, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_3, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_nat_add(x_42, x_56);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_4);
lean_ctor_set(x_63, 2, x_60);
x_64 = lean_array_uset(x_43, x_59, x_63);
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_shiftl(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__1___redArg(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_64);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_box(0);
x_75 = lean_array_uset(x_43, x_59, x_74);
x_76 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__4___redArg(x_3, x_4, x_60);
x_77 = lean_array_uset(x_75, x_59, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_42);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
case 1:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_1, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_1, 3);
lean_inc(x_155);
lean_dec(x_1);
x_156 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_155, x_2);
x_1 = x_154;
x_2 = x_156;
goto _start;
}
case 10:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_1, 3);
lean_inc(x_158);
lean_dec(x_1);
x_159 = lean_unsigned_to_nat(0u);
x_160 = lean_array_get_size(x_158);
x_161 = lean_nat_dec_lt(x_159, x_160);
if (x_161 == 0)
{
lean_dec(x_160);
lean_dec(x_158);
return x_2;
}
else
{
uint8_t x_162; 
x_162 = lean_nat_dec_le(x_160, x_160);
if (x_162 == 0)
{
lean_dec(x_160);
lean_dec(x_158);
return x_2;
}
else
{
size_t x_163; size_t x_164; lean_object* x_165; 
x_163 = lean_usize_of_nat(x_159);
x_164 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_165 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(x_158, x_163, x_164, x_2);
lean_dec(x_158);
return x_165;
}
}
}
default: 
{
uint8_t x_166; 
x_166 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_166 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_1, 3);
lean_inc(x_167);
lean_dec(x_1);
x_1 = x_167;
goto _start;
}
case 1:
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_1, 3);
lean_inc(x_169);
lean_dec(x_1);
x_1 = x_169;
goto _start;
}
case 2:
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_1, 3);
lean_inc(x_171);
lean_dec(x_1);
x_1 = x_171;
goto _start;
}
case 3:
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_1, 2);
lean_inc(x_173);
lean_dec(x_1);
x_1 = x_173;
goto _start;
}
case 4:
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_1, 3);
lean_inc(x_175);
lean_dec(x_1);
x_1 = x_175;
goto _start;
}
case 5:
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_1, 5);
lean_inc(x_177);
lean_dec(x_1);
x_1 = x_177;
goto _start;
}
case 6:
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_1, 2);
lean_inc(x_179);
lean_dec(x_1);
x_1 = x_179;
goto _start;
}
case 7:
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_1, 2);
lean_inc(x_181);
lean_dec(x_1);
x_1 = x_181;
goto _start;
}
case 8:
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_1, 1);
lean_inc(x_183);
lean_dec(x_1);
x_1 = x_183;
goto _start;
}
case 9:
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_1, 1);
lean_inc(x_185);
lean_dec(x_1);
x_1 = x_185;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_shiftl(x_3, x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_nat_div(x_6, x_7);
lean_dec(x_6);
x_9 = l_Nat_nextPowerOfTwo(x_8);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(8u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_shiftl(x_14, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_div(x_17, x_18);
lean_dec(x_17);
x_20 = l_Nat_nextPowerOfTwo(x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_mk_array(x_20, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_15; 
x_6 = lean_box(1);
x_15 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_16);
lean_dec(x_16);
x_7 = x_17;
goto block_14;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_18);
lean_dec(x_18);
x_7 = x_19;
goto block_14;
}
block_14:
{
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
if (x_5 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_6);
return x_13;
}
}
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 3);
x_2 = x_8;
goto _start;
}
}
case 7:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_nat_dec_eq(x_1, x_10);
if (x_12 == 0)
{
x_2 = x_11;
goto _start;
}
else
{
return x_12;
}
}
case 10:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
return x_19;
}
else
{
if (x_17 == 0)
{
lean_dec(x_16);
return x_17;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_usize_of_nat(x_15);
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(x_1, x_14, x_20, x_21);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
}
default: 
{
uint8_t x_25; 
x_25 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_25 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 3);
x_2 = x_26;
goto _start;
}
case 1:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 3);
x_2 = x_28;
goto _start;
}
case 2:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 3);
x_2 = x_30;
goto _start;
}
case 3:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 2);
x_2 = x_32;
goto _start;
}
case 4:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_2, 3);
x_2 = x_34;
goto _start;
}
case 5:
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_2, 5);
x_2 = x_36;
goto _start;
}
case 6:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_2, 2);
x_2 = x_38;
goto _start;
}
case 7:
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_2, 2);
x_2 = x_40;
goto _start;
}
case 8:
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_2, 1);
x_2 = x_42;
goto _start;
}
case 9:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 1);
x_2 = x_44;
goto _start;
}
default: 
{
goto _start;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_IR_ExpandResetReuse_consumed_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_nat_dec_eq(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_10 = lean_uint64_of_nat(x_7);
lean_dec(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_1, x_25);
lean_ctor_set(x_2, 2, x_26);
x_27 = lean_array_uset(x_1, x_25, x_2);
x_1 = x_27;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
x_34 = lean_array_get_size(x_1);
x_35 = lean_uint64_of_nat(x_32);
lean_dec(x_32);
x_36 = lean_uint64_of_nat(x_33);
lean_dec(x_33);
x_37 = lean_uint64_mix_hash(x_35, x_36);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_1, x_51);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_29);
lean_ctor_set(x_53, 1, x_30);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_array_uset(x_1, x_51, x_53);
x_1 = x_54;
x_2 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4___lam__0(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_10 = x_2;
} else {
 lean_dec_ref(x_2);
 x_10 = lean_box(0);
}
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_nat_dec_eq(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_11 = x_23;
goto block_18;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
x_11 = x_24;
goto block_18;
}
block_18:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4(x_1, x_9);
if (lean_is_scalar(x_10)) {
 x_13 = lean_alloc_ctor(1, 3, 0);
} else {
 x_13 = x_10;
}
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4___lam__0(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_is_scalar(x_10)) {
 x_17 = lean_alloc_ctor(1, 3, 0);
} else {
 x_17 = x_10;
}
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_9);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 3)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_19 = x_4;
} else {
 lean_dec_ref(x_4);
 x_19 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_16);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 1, x_15);
lean_ctor_set(x_13, 0, x_16);
x_20 = lean_array_get_size(x_18);
x_21 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_22 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_sub(x_33, x_35);
x_37 = lean_usize_land(x_32, x_36);
x_38 = lean_array_uget(x_18, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_13, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_40 = lean_nat_add(x_17, x_34);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_13);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_38);
x_42 = lean_array_uset(x_18, x_37, x_41);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_shiftl(x_40, x_43);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_div(x_44, x_45);
lean_dec(x_44);
x_47 = lean_array_get_size(x_42);
x_48 = lean_nat_dec_le(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1___redArg(x_42);
if (lean_is_scalar(x_19)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_19;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_5 = x_50;
goto block_10;
}
else
{
lean_object* x_51; 
if (lean_is_scalar(x_19)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_19;
}
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_42);
x_5 = x_51;
goto block_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_59; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_18, x_37, x_52);
lean_inc(x_13);
x_54 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4(x_13, x_38);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_13, x_54);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_nat_sub(x_17, x_34);
lean_dec(x_17);
x_55 = x_60;
goto block_58;
}
else
{
x_55 = x_17;
goto block_58;
}
block_58:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_uset(x_53, x_37, x_54);
if (lean_is_scalar(x_19)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_19;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_5 = x_57;
goto block_10;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; lean_object* x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_61 = lean_ctor_get(x_13, 0);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_13);
x_63 = lean_ctor_get(x_4, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_65 = x_4;
} else {
 lean_dec_ref(x_4);
 x_65 = lean_box(0);
}
lean_inc(x_61);
lean_inc(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_61);
x_67 = lean_array_get_size(x_64);
x_68 = lean_uint64_of_nat(x_62);
lean_dec(x_62);
x_69 = lean_uint64_of_nat(x_61);
lean_dec(x_61);
x_70 = lean_uint64_mix_hash(x_68, x_69);
x_71 = lean_unsigned_to_nat(32u);
x_72 = lean_uint64_of_nat(x_71);
x_73 = lean_uint64_shift_right(x_70, x_72);
x_74 = lean_uint64_xor(x_70, x_73);
x_75 = lean_unsigned_to_nat(16u);
x_76 = lean_uint64_of_nat(x_75);
x_77 = lean_uint64_shift_right(x_74, x_76);
x_78 = lean_uint64_xor(x_74, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_usize_of_nat(x_81);
x_83 = lean_usize_sub(x_80, x_82);
x_84 = lean_usize_land(x_79, x_83);
x_85 = lean_array_uget(x_64, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_66, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_nat_add(x_63, x_81);
lean_dec(x_63);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_66);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_85);
x_89 = lean_array_uset(x_64, x_84, x_88);
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_nat_shiftl(x_87, x_90);
x_92 = lean_unsigned_to_nat(3u);
x_93 = lean_nat_div(x_91, x_92);
lean_dec(x_91);
x_94 = lean_array_get_size(x_89);
x_95 = lean_nat_dec_le(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1___redArg(x_89);
if (lean_is_scalar(x_65)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_65;
}
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_5 = x_97;
goto block_10;
}
else
{
lean_object* x_98; 
if (lean_is_scalar(x_65)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_65;
}
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
x_5 = x_98;
goto block_10;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_106; 
x_99 = lean_box(0);
x_100 = lean_array_uset(x_64, x_84, x_99);
lean_inc(x_66);
x_101 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4(x_66, x_85);
x_106 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_66, x_101);
lean_dec(x_66);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_nat_sub(x_63, x_81);
lean_dec(x_63);
x_102 = x_107;
goto block_105;
}
else
{
x_102 = x_63;
goto block_105;
}
block_105:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_array_uset(x_100, x_84, x_101);
if (lean_is_scalar(x_65)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_65;
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_5 = x_104;
goto block_10;
}
}
}
}
else
{
lean_dec(x_13);
x_5 = x_4;
goto block_10;
}
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 3)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_19 = x_4;
} else {
 lean_dec_ref(x_4);
 x_19 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_16);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 1, x_15);
lean_ctor_set(x_13, 0, x_16);
x_20 = lean_array_get_size(x_18);
x_21 = lean_uint64_of_nat(x_16);
lean_dec(x_16);
x_22 = lean_uint64_of_nat(x_15);
lean_dec(x_15);
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_sub(x_33, x_35);
x_37 = lean_usize_land(x_32, x_36);
x_38 = lean_array_uget(x_18, x_37);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_13, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_40 = lean_nat_add(x_17, x_34);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_13);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_38);
x_42 = lean_array_uset(x_18, x_37, x_41);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_shiftl(x_40, x_43);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_div(x_44, x_45);
lean_dec(x_44);
x_47 = lean_array_get_size(x_42);
x_48 = lean_nat_dec_le(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1___redArg(x_42);
if (lean_is_scalar(x_19)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_19;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_5 = x_50;
goto block_10;
}
else
{
lean_object* x_51; 
if (lean_is_scalar(x_19)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_19;
}
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_42);
x_5 = x_51;
goto block_10;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_59; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_18, x_37, x_52);
lean_inc(x_13);
x_54 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4(x_13, x_38);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_13, x_54);
lean_dec(x_13);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_nat_sub(x_17, x_34);
lean_dec(x_17);
x_55 = x_60;
goto block_58;
}
else
{
x_55 = x_17;
goto block_58;
}
block_58:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_uset(x_53, x_37, x_54);
if (lean_is_scalar(x_19)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_19;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_5 = x_57;
goto block_10;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; lean_object* x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_61 = lean_ctor_get(x_13, 0);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_13);
x_63 = lean_ctor_get(x_4, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_65 = x_4;
} else {
 lean_dec_ref(x_4);
 x_65 = lean_box(0);
}
lean_inc(x_61);
lean_inc(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_61);
x_67 = lean_array_get_size(x_64);
x_68 = lean_uint64_of_nat(x_62);
lean_dec(x_62);
x_69 = lean_uint64_of_nat(x_61);
lean_dec(x_61);
x_70 = lean_uint64_mix_hash(x_68, x_69);
x_71 = lean_unsigned_to_nat(32u);
x_72 = lean_uint64_of_nat(x_71);
x_73 = lean_uint64_shift_right(x_70, x_72);
x_74 = lean_uint64_xor(x_70, x_73);
x_75 = lean_unsigned_to_nat(16u);
x_76 = lean_uint64_of_nat(x_75);
x_77 = lean_uint64_shift_right(x_74, x_76);
x_78 = lean_uint64_xor(x_74, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_usize_of_nat(x_81);
x_83 = lean_usize_sub(x_80, x_82);
x_84 = lean_usize_land(x_79, x_83);
x_85 = lean_array_uget(x_64, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_66, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_nat_add(x_63, x_81);
lean_dec(x_63);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_66);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_85);
x_89 = lean_array_uset(x_64, x_84, x_88);
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_nat_shiftl(x_87, x_90);
x_92 = lean_unsigned_to_nat(3u);
x_93 = lean_nat_div(x_91, x_92);
lean_dec(x_91);
x_94 = lean_array_get_size(x_89);
x_95 = lean_nat_dec_le(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__1___redArg(x_89);
if (lean_is_scalar(x_65)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_65;
}
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_5 = x_97;
goto block_10;
}
else
{
lean_object* x_98; 
if (lean_is_scalar(x_65)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_65;
}
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
x_5 = x_98;
goto block_10;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_106; 
x_99 = lean_box(0);
x_100 = lean_array_uset(x_64, x_84, x_99);
lean_inc(x_66);
x_101 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__4(x_66, x_85);
x_106 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_66, x_101);
lean_dec(x_66);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_nat_sub(x_63, x_81);
lean_dec(x_63);
x_102 = x_107;
goto block_105;
}
else
{
x_102 = x_63;
goto block_105;
}
block_105:
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_array_uset(x_100, x_84, x_101);
if (lean_is_scalar(x_65)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_65;
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_5 = x_104;
goto block_10;
}
}
}
}
else
{
lean_dec(x_13);
x_5 = x_4;
goto block_10;
}
}
else
{
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5_spec__5(x_1, x_8, x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_computeProjCounts(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_shiftl(x_2, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_div(x_5, x_6);
lean_dec(x_5);
x_8 = l_Nat_nextPowerOfTwo(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
return x_11;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_12, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
return x_11;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_3);
x_16 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_17 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5(x_1, x_15, x_16, x_11);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_computeProjCounts_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_computeProjCounts___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_computeProjCounts(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
x_5 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
x_6 = lean_unsigned_to_nat(138u);
x_7 = lean_unsigned_to_nat(11u);
x_8 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_panic_fn(x_1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_nat_dec_eq(x_17, x_19);
if (x_21 == 0)
{
x_14 = x_21;
goto block_16;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_18, x_20);
x_14 = x_22;
goto block_16;
}
block_16:
{
if (x_14 == 0)
{
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_12);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Array_reverse(lean_box(0), x_1);
x_6 = l_Array_append(lean_box(0), x_2, x_5);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_array_get_size(x_2);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_IR_instInhabitedFnBody;
x_24 = l_Array_back_x21(lean_box(0), x_23, x_2);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
switch (lean_obj_tag(x_25)) {
case 4:
{
lean_dec(x_25);
x_6 = x_24;
goto block_10;
}
case 5:
{
lean_dec(x_25);
x_6 = x_24;
goto block_10;
}
default: 
{
lean_dec(x_25);
lean_dec(x_24);
goto block_13;
}
}
}
case 6:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_24, sizeof(void*)*3);
x_29 = lean_ctor_get_uint8(x_24, sizeof(void*)*3 + 1);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_27, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_34 = lean_array_fget(x_2, x_33);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 3)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_78; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_78 = lean_nat_dec_eq(x_36, x_26);
lean_dec(x_36);
if (x_78 == 0)
{
x_40 = x_78;
goto block_77;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_eq(x_1, x_38);
x_40 = x_79;
goto block_77;
}
block_77:
{
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
goto block_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; size_t x_56; size_t x_57; lean_object* x_58; size_t x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_41 = lean_ctor_get(x_3, 1);
x_42 = l_instInhabitedNat;
lean_inc(x_37);
lean_inc(x_38);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_39;
 lean_ctor_set_tag(x_43, 0);
}
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_37);
x_44 = lean_array_get_size(x_41);
x_45 = lean_uint64_of_nat(x_38);
lean_dec(x_38);
x_46 = lean_uint64_of_nat(x_37);
x_47 = lean_uint64_mix_hash(x_45, x_46);
x_48 = lean_unsigned_to_nat(32u);
x_49 = lean_uint64_of_nat(x_48);
x_50 = lean_uint64_shift_right(x_47, x_49);
x_51 = lean_uint64_xor(x_47, x_50);
x_52 = lean_unsigned_to_nat(16u);
x_53 = lean_uint64_of_nat(x_52);
x_54 = lean_uint64_shift_right(x_51, x_53);
x_55 = lean_uint64_xor(x_51, x_54);
x_56 = lean_uint64_to_usize(x_55);
x_57 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_usize_of_nat(x_58);
x_60 = lean_usize_sub(x_57, x_59);
x_61 = lean_usize_land(x_56, x_60);
x_62 = lean_array_uget(x_41, x_61);
x_63 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___redArg(x_42, x_43, x_62);
lean_dec(x_62);
lean_dec(x_43);
x_64 = lean_nat_dec_eq(x_63, x_58);
lean_dec(x_63);
if (x_64 == 0)
{
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
goto block_19;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_array_pop(x_2);
x_66 = lean_array_pop(x_65);
lean_inc(x_26);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_26);
x_68 = lean_array_set(x_4, x_37, x_67);
lean_dec(x_37);
x_69 = lean_array_push(x_5, x_34);
x_70 = lean_nat_dec_eq(x_27, x_58);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_nat_sub(x_27, x_58);
lean_dec(x_27);
x_72 = lean_box(13);
if (lean_is_scalar(x_30)) {
 x_73 = lean_alloc_ctor(6, 3, 2);
} else {
 x_73 = x_30;
}
lean_ctor_set(x_73, 0, x_26);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_28);
lean_ctor_set_uint8(x_73, sizeof(void*)*3 + 1, x_29);
x_74 = lean_array_push(x_69, x_73);
x_2 = x_66;
x_4 = x_68;
x_5 = x_74;
goto _start;
}
else
{
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
x_2 = x_66;
x_4 = x_68;
x_5 = x_69;
goto _start;
}
}
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
goto block_16;
}
}
else
{
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
goto block_16;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_20);
x_80 = lean_box(0);
x_81 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_5, x_2, x_4, x_80);
return x_81;
}
}
default: 
{
lean_dec(x_24);
lean_dec(x_20);
goto block_13;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_20);
x_82 = lean_box(0);
x_83 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_5, x_2, x_4, x_82);
return x_83;
}
block_10:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_pop(x_2);
x_8 = lean_array_push(x_5, x_6);
x_2 = x_7;
x_5 = x_8;
goto _start;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_5, x_2, x_4, x_11);
return x_12;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_5, x_2, x_4, x_14);
return x_15;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_5, x_2, x_4, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_IR_ExpandResetReuse_eraseProjIncForAux_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_IR_ExpandResetReuse_computeProjCounts(x_3);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_1, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_2, x_3, x_4, x_6, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_17);
lean_ctor_set(x_6, 1, x_18);
x_9 = x_6;
goto block_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_9 = x_22;
goto block_15;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_24);
lean_ctor_set(x_6, 0, x_25);
x_9 = x_6;
goto block_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_9 = x_28;
goto block_15;
}
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
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
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_1, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
x_17 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_11);
lean_ctor_set(x_2, 3, x_17);
return x_2;
}
else
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_2, 2, x_18);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_1, x_22);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
x_26 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_21);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_9);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_21);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_2, 3);
x_32 = lean_ctor_get(x_2, 2);
lean_dec(x_32);
x_33 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_31);
lean_ctor_set(x_2, 3, x_33);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_37 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_9);
lean_ctor_set(x_38, 3, x_37);
return x_38;
}
}
}
case 7:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_2);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_nat_dec_eq(x_1, x_40);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_42);
lean_ctor_set(x_2, 2, x_44);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_41);
lean_dec(x_40);
return x_42;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_50 = lean_nat_dec_eq(x_1, x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_49);
x_52 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*3 + 1, x_48);
return x_52;
}
else
{
lean_dec(x_46);
lean_dec(x_45);
return x_49;
}
}
}
case 10:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; size_t x_55; lean_object* x_56; size_t x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_2, 3);
x_55 = lean_array_size(x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_usize_of_nat(x_56);
x_58 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(x_1, x_55, x_57, x_54);
lean_ctor_set(x_2, 3, x_58);
return x_2;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_ctor_get(x_2, 2);
x_62 = lean_ctor_get(x_2, 3);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_2);
x_63 = lean_array_size(x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_usize_of_nat(x_64);
x_66 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(x_1, x_63, x_65, x_62);
x_67 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_66);
return x_67;
}
}
default: 
{
uint8_t x_68; 
x_68 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_68 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_2, 3);
lean_inc(x_69);
x_3 = x_69;
goto block_8;
}
case 1:
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_2, 3);
lean_inc(x_70);
x_3 = x_70;
goto block_8;
}
case 2:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_2, 3);
lean_inc(x_71);
x_3 = x_71;
goto block_8;
}
case 3:
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_2, 2);
lean_inc(x_72);
x_3 = x_72;
goto block_8;
}
case 4:
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_2, 3);
lean_inc(x_73);
x_3 = x_73;
goto block_8;
}
case 5:
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 5);
lean_inc(x_74);
x_3 = x_74;
goto block_8;
}
case 6:
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_3 = x_75;
goto block_8;
}
case 7:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_2, 2);
lean_inc(x_76);
x_3 = x_76;
goto block_8;
}
case 8:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_3 = x_77;
goto block_8;
}
case 9:
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_3 = x_78;
goto block_8;
}
default: 
{
lean_inc(x_2);
x_3 = x_2;
goto block_8;
}
}
}
else
{
return x_2;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(13);
x_5 = l_Lean_IR_FnBody_setBody(x_2, x_4);
x_6 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_3);
x_7 = l_Lean_IR_FnBody_setBody(x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToCtor_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_12 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
x_7 = x_4;
goto block_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_4);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_16);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_5);
x_7 = x_15;
goto block_11;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = lean_usize_of_nat(x_6);
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_10);
x_11 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_3);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_12);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(x_3, x_16, x_17, x_9);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExpandResetReuse_mkSlowPath_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_mkFresh___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_mkFresh(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_array_fget(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_IR_ExpandResetReuse_mkFresh___redArg(x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(7);
lean_inc(x_2);
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 0, x_13);
x_20 = lean_box(1);
lean_inc(x_17);
x_21 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_5);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_8);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_21);
x_4 = x_11;
x_5 = x_23;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_box(7);
lean_inc(x_2);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_box(1);
lean_inc(x_25);
x_30 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_5);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_8);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_30);
x_4 = x_11;
x_5 = x_32;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(x_2, x_1, x_6, x_6, x_3, x_5);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at___Lean_IR_ExpandResetReuse_releaseUnreadFields_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = lean_array_fget(x_1, x_10);
lean_inc(x_2);
x_12 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_5);
x_4 = x_9;
x_5 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(x_2, x_1, x_4, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at___Lean_IR_ExpandResetReuse_setFields_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_setFields(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_nat_dec_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_5);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_6, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_5, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 3)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_nat_dec_eq(x_28, x_3);
lean_dec(x_28);
if (x_30 == 0)
{
lean_dec(x_29);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_eq(x_29, x_2);
lean_dec(x_29);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_uint64_of_nat(x_4);
x_8 = lean_unsigned_to_nat(32u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = lean_unsigned_to_nat(16u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_sub(x_17, x_19);
x_21 = lean_usize_land(x_16, x_20);
x_22 = lean_array_uget(x_5, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_4, x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_dec_eq(x_27, x_3);
lean_dec(x_27);
if (x_29 == 0)
{
lean_dec(x_28);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_eq(x_28, x_2);
lean_dec(x_28);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; lean_object* x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_5);
x_9 = lean_unsigned_to_nat(32u);
x_10 = lean_uint64_of_nat(x_9);
x_11 = lean_uint64_shift_right(x_8, x_10);
x_12 = lean_uint64_xor(x_8, x_11);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_sub(x_18, x_20);
x_22 = lean_usize_land(x_17, x_21);
x_23 = lean_array_uget(x_6, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_IR_ExpandResetReuse_isSelfSet_spec__0___redArg(x_5, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 5)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 2);
lean_inc(x_30);
lean_dec(x_27);
x_34 = lean_nat_dec_eq(x_3, x_28);
lean_dec(x_28);
if (x_34 == 0)
{
lean_dec(x_29);
x_31 = x_34;
goto block_33;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_eq(x_29, x_4);
lean_dec(x_29);
x_31 = x_35;
goto block_33;
}
block_33:
{
if (x_31 == 0)
{
lean_dec(x_30);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_eq(x_30, x_2);
lean_dec(x_30);
return x_32;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_27);
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_17);
lean_ctor_set(x_6, 1, x_18);
x_9 = x_6;
goto block_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_9 = x_22;
goto block_15;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_24);
lean_ctor_set(x_6, 0, x_25);
x_9 = x_6;
goto block_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_9 = x_28;
goto block_15;
}
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
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
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_10, x_11, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_13);
lean_ctor_set(x_2, 3, x_15);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_2 = x_13;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_21 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_17, x_18, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_20);
x_23 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_22);
return x_23;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_2 = x_20;
goto _start;
}
}
}
case 4:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_ctor_get(x_2, 3);
x_30 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_26, x_27, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_29);
lean_ctor_set(x_2, 3, x_31);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_2 = x_29;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_37 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_33, x_34, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_36);
x_39 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_38);
return x_39;
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_2 = x_36;
goto _start;
}
}
}
case 5:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get(x_2, 3);
x_46 = lean_ctor_get(x_2, 4);
x_47 = lean_ctor_get(x_2, 5);
x_48 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_42, x_43, x_44, x_45);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_47);
lean_ctor_set(x_2, 5, x_49);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_2 = x_47;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 3);
x_55 = lean_ctor_get(x_2, 4);
x_56 = lean_ctor_get(x_2, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_57 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_51, x_52, x_53, x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_56);
x_59 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_54);
lean_ctor_set(x_59, 4, x_55);
lean_ctor_set(x_59, 5, x_58);
return x_59;
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_2 = x_56;
goto _start;
}
}
}
case 10:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_2, 3);
x_63 = lean_array_size(x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_usize_of_nat(x_64);
x_66 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(x_1, x_63, x_65, x_62);
lean_ctor_set(x_2, 3, x_66);
return x_2;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; lean_object* x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_69 = lean_ctor_get(x_2, 2);
x_70 = lean_ctor_get(x_2, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_2);
x_71 = lean_array_size(x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_usize_of_nat(x_72);
x_74 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(x_1, x_71, x_73, x_70);
x_75 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_69);
lean_ctor_set(x_75, 3, x_74);
return x_75;
}
}
default: 
{
uint8_t x_76; 
x_76 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_76 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_2, 3);
lean_inc(x_77);
x_3 = x_77;
goto block_8;
}
case 1:
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 3);
lean_inc(x_78);
x_3 = x_78;
goto block_8;
}
case 2:
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_2, 3);
lean_inc(x_79);
x_3 = x_79;
goto block_8;
}
case 3:
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_2, 2);
lean_inc(x_80);
x_3 = x_80;
goto block_8;
}
case 4:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 3);
lean_inc(x_81);
x_3 = x_81;
goto block_8;
}
case 5:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_2, 5);
lean_inc(x_82);
x_3 = x_82;
goto block_8;
}
case 6:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_2, 2);
lean_inc(x_83);
x_3 = x_83;
goto block_8;
}
case 7:
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_2, 2);
lean_inc(x_84);
x_3 = x_84;
goto block_8;
}
case 8:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_3 = x_85;
goto block_8;
}
case 9:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_2, 1);
lean_inc(x_86);
x_3 = x_86;
goto block_8;
}
default: 
{
lean_inc(x_2);
x_3 = x_2;
goto block_8;
}
}
}
else
{
return x_2;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(13);
x_5 = l_Lean_IR_FnBody_setBody(x_2, x_4);
x_6 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_3);
x_7 = l_Lean_IR_FnBody_setBody(x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_removeSelfSet_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_6, x_5, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_3);
x_20 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_19);
lean_ctor_set(x_8, 1, x_20);
x_11 = x_8;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
lean_inc(x_3);
x_23 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_11 = x_24;
goto block_17;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_3);
x_27 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_26);
lean_ctor_set(x_8, 0, x_27);
x_11 = x_8;
goto block_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
lean_inc(x_3);
x_29 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_11 = x_30;
goto block_17;
}
}
block_17:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_5, x_13);
x_15 = lean_array_uset(x_10, x_5, x_11);
x_5 = x_14;
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 2)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_20 = lean_ctor_get(x_11, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_eq(x_2, x_17);
lean_dec(x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_15);
lean_ctor_set(x_4, 3, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_11);
lean_inc(x_3);
x_23 = l_Lean_IR_FnBody_replaceVar(x_13, x_3, x_15);
lean_inc(x_3);
x_24 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_20, x_23);
lean_dec(x_20);
if (x_19 == 0)
{
lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_3);
x_25 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
x_28 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_ctor_get(x_4, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_35 = lean_ctor_get(x_11, 2);
lean_inc(x_35);
x_36 = lean_nat_dec_eq(x_2, x_32);
lean_dec(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_33);
x_37 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_31);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_11);
lean_ctor_set(x_38, 3, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_11);
lean_inc(x_3);
x_39 = l_Lean_IR_FnBody_replaceVar(x_29, x_3, x_31);
lean_inc(x_3);
x_40 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_35, x_39);
lean_dec(x_35);
if (x_34 == 0)
{
lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_3);
x_41 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
x_44 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_4, 3);
x_47 = lean_ctor_get(x_4, 2);
lean_dec(x_47);
x_48 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_46);
lean_ctor_set(x_4, 3, x_48);
return x_4;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
x_51 = lean_ctor_get(x_4, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_4);
x_52 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_51);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_11);
lean_ctor_set(x_53, 3, x_52);
return x_53;
}
}
}
case 7:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_4);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
x_57 = lean_ctor_get(x_4, 2);
x_58 = lean_nat_dec_eq(x_2, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_57);
lean_ctor_set(x_4, 2, x_59);
return x_4;
}
else
{
lean_object* x_60; 
lean_free_object(x_4);
lean_dec(x_56);
lean_dec(x_55);
x_60 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
x_63 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_65 = lean_ctor_get(x_4, 2);
lean_inc(x_65);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_66 = lean_nat_dec_eq(x_2, x_61);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_65);
x_68 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*3 + 1, x_64);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_61);
x_69 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
}
case 10:
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_4);
if (x_70 == 0)
{
lean_object* x_71; size_t x_72; lean_object* x_73; size_t x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_4, 3);
x_72 = lean_array_size(x_71);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_usize_of_nat(x_73);
x_75 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(x_1, x_2, x_3, x_72, x_74, x_71);
lean_ctor_set(x_4, 3, x_75);
return x_4;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; lean_object* x_81; size_t x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_4, 0);
x_77 = lean_ctor_get(x_4, 1);
x_78 = lean_ctor_get(x_4, 2);
x_79 = lean_ctor_get(x_4, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_4);
x_80 = lean_array_size(x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_usize_of_nat(x_81);
x_83 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(x_1, x_2, x_3, x_80, x_82, x_79);
x_84 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_83);
return x_84;
}
}
default: 
{
uint8_t x_85; 
x_85 = l_Lean_IR_FnBody_isTerminal(x_4);
if (x_85 == 0)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_4, 3);
lean_inc(x_86);
x_5 = x_86;
goto block_10;
}
case 1:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_4, 3);
lean_inc(x_87);
x_5 = x_87;
goto block_10;
}
case 2:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_4, 3);
lean_inc(x_88);
x_5 = x_88;
goto block_10;
}
case 3:
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_4, 2);
lean_inc(x_89);
x_5 = x_89;
goto block_10;
}
case 4:
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_4, 3);
lean_inc(x_90);
x_5 = x_90;
goto block_10;
}
case 5:
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_4, 5);
lean_inc(x_91);
x_5 = x_91;
goto block_10;
}
case 6:
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
x_5 = x_92;
goto block_10;
}
case 7:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_4, 2);
lean_inc(x_93);
x_5 = x_93;
goto block_10;
}
case 8:
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_4, 1);
lean_inc(x_94);
x_5 = x_94;
goto block_10;
}
case 9:
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_4, 1);
lean_inc(x_95);
x_5 = x_95;
goto block_10;
}
default: 
{
lean_inc(x_4);
x_5 = x_4;
goto block_10;
}
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(13);
x_7 = l_Lean_IR_FnBody_setBody(x_4, x_6);
x_8 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_5);
x_9 = l_Lean_IR_FnBody_setBody(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_reuseToSet_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_7 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_5, x_1, x_2, x_4);
x_8 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_4, x_5, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_3, x_5, x_11, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_apply_4(x_1, x_13, x_16, x_7, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_ExpandResetReuse_mkFresh___redArg(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_5);
x_23 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean_dec(x_11);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_25, 0, x_5);
lean_inc(x_22);
x_26 = l_Lean_IR_mkIf(x_22, x_23, x_18);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_IR_reshape(x_10, x_27);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
lean_inc(x_5);
x_31 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean_dec(x_11);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_33, 0, x_5);
lean_inc(x_29);
x_34 = l_Lean_IR_mkIf(x_29, x_31, x_18);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
x_36 = l_Lean_IR_reshape(x_10, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExpandResetReuse_expand(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_1, x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_3, x_2, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_4);
x_21 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___lam__0(x_20, x_4, x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_8, 1, x_22);
x_11 = x_8;
x_12 = x_23;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
lean_inc(x_4);
x_26 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___lam__0(x_25, x_4, x_5);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_27);
x_11 = x_29;
x_12 = x_28;
goto block_18;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_4);
x_32 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___lam__0(x_31, x_4, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set(x_8, 0, x_33);
x_11 = x_8;
x_12 = x_34;
goto block_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
lean_inc(x_4);
x_36 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___lam__0(x_35, x_4, x_5);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_11 = x_39;
x_12 = x_38;
goto block_18;
}
}
block_18:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_10, x_2, x_11);
x_2 = x_15;
x_3 = x_16;
x_5 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_IR_ExpandResetReuse_consumed(x_32, x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
x_37 = l_Lean_IR_push(x_2, x_1);
x_1 = x_33;
x_2 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_searchAndExpand), 4, 0);
x_40 = l_Lean_IR_ExpandResetReuse_expand(x_39, x_2, x_32, x_34, x_35, x_33, x_3, x_4);
lean_dec(x_32);
return x_40;
}
}
else
{
lean_dec(x_31);
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_30;
}
}
case 1:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_1, 2);
x_43 = lean_ctor_get(x_1, 3);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_mk_empty_array_with_capacity(x_44);
lean_inc(x_3);
x_46 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_42, x_45, x_3, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(13);
lean_ctor_set(x_1, 3, x_49);
lean_ctor_set(x_1, 2, x_47);
x_50 = l_Lean_IR_push(x_2, x_1);
x_1 = x_43;
x_2 = x_50;
x_4 = x_48;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_54 = lean_ctor_get(x_1, 2);
x_55 = lean_ctor_get(x_1, 3);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_mk_empty_array_with_capacity(x_56);
lean_inc(x_3);
x_58 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_54, x_57, x_3, x_4);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_box(13);
x_62 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = l_Lean_IR_push(x_2, x_62);
x_1 = x_55;
x_2 = x_63;
x_4 = x_60;
goto _start;
}
}
case 10:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; size_t x_67; lean_object* x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_1, 3);
x_67 = lean_array_size(x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_usize_of_nat(x_68);
x_70 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(x_67, x_69, x_66, x_3, x_4);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_ctor_set(x_1, 3, x_72);
x_73 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
lean_ctor_set(x_1, 3, x_74);
x_76 = l_Lean_IR_reshape(x_2, x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
x_80 = lean_ctor_get(x_1, 2);
x_81 = lean_ctor_get(x_1, 3);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_1);
x_82 = lean_array_size(x_81);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_usize_of_nat(x_83);
x_85 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(x_82, x_84, x_81, x_3, x_4);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_79);
lean_ctor_set(x_89, 2, x_80);
lean_ctor_set(x_89, 3, x_86);
x_90 = l_Lean_IR_reshape(x_2, x_89);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
}
default: 
{
x_13 = x_1;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
goto block_30;
}
}
block_12:
{
lean_object* x_10; 
x_10 = l_Lean_IR_push(x_5, x_7);
x_1 = x_9;
x_2 = x_10;
x_3 = x_8;
x_4 = x_6;
goto _start;
}
block_30:
{
uint8_t x_17; 
x_17 = l_Lean_IR_FnBody_isTerminal(x_13);
if (x_17 == 0)
{
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_18);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_18;
goto block_12;
}
case 1:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_19;
goto block_12;
}
case 2:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 3);
lean_inc(x_20);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_20;
goto block_12;
}
case 3:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_21;
goto block_12;
}
case 4:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_13, 3);
lean_inc(x_22);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_22;
goto block_12;
}
case 5:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_13, 5);
lean_inc(x_23);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_23;
goto block_12;
}
case 6:
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_24;
goto block_12;
}
case 7:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_13, 2);
lean_inc(x_25);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_25;
goto block_12;
}
case 8:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_26;
goto block_12;
}
case 9:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_27;
goto block_12;
}
default: 
{
lean_inc(x_13);
x_5 = x_14;
x_6 = x_16;
x_7 = x_13;
x_8 = x_15;
x_9 = x_13;
goto block_12;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
x_28 = l_Lean_IR_reshape(x_14, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_ExpandResetReuse_searchAndExpand_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_IR_Decl_maxIndex(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
lean_inc(x_1);
x_8 = l_Lean_IR_ExpandResetReuse_mkProjMap(x_1);
x_9 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_2, x_7, x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_Decl_updateBody_x21(x_1, x_10);
return x_11;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_main(x_1);
x_3 = l_Lean_IR_Decl_normalizeIds(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
