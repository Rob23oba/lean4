// Lean compiler output
// Module: Lean.Replay
// Imports: Lean.CoreM Lean.AddDecl Lean.Util.FoldConsts
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
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstantInfo;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
uint8_t l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3023_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstants(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3455_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = l_Lean_Name_quickCmp(x_1, x_5);
switch (x_8) {
case 0:
{
uint8_t x_9; 
x_9 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_box(0);
x_11 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_4);
x_14 = l_Lean_RBNode_balLeft___redArg(x_13, x_5, x_6, x_7);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_15 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_box(0);
x_18 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_18);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_7);
x_21 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_4, x_5, x_6, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_26 = l_Lean_Name_quickCmp(x_1, x_23);
switch (x_26) {
case 0:
{
uint8_t x_27; 
x_27 = l_Lean_RBNode_isBlack___redArg(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_box(0);
x_29 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_22);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
x_31 = lean_unbox(x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_22);
x_33 = l_Lean_RBNode_balLeft___redArg(x_32, x_23, x_24, x_25);
return x_33;
}
}
case 1:
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
x_34 = l_Lean_RBNode_appendTrees___redArg(x_22, x_25);
return x_34;
}
default: 
{
uint8_t x_35; 
x_35 = l_Lean_RBNode_isBlack___redArg(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_box(0);
x_37 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_25);
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_unbox(x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_39);
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_25);
x_41 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_22, x_23, x_24, x_40);
return x_41;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_NameSet_contains(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_4);
x_11 = lean_st_ref_take(x_2, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_14);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = l_Lean_NameSet_insert(x_17, x_1);
x_19 = lean_ctor_get(x_12, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 4);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_st_ref_set(x_2, x_21, x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(x_9);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_NameSet_contains(x_31, x_1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_st_ref_take(x_2, x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_38);
x_41 = lean_ctor_get(x_36, 2);
lean_inc(x_41);
x_42 = l_Lean_NameSet_insert(x_41, x_1);
x_43 = lean_ctor_get(x_36, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_36, 4);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_st_ref_set(x_2, x_45, x_37);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(x_32);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_isTodo___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_isTodo___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_isTodo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_isTodo(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_box(0);
x_4 = l_Lean_Kernel_Exception_toMessageData(x_1, x_3);
x_5 = l_Lean_MessageData_toString(x_4, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_throwKernelException___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_throwKernelException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_throwKernelException(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_box(0);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Environment_addDeclCore(x_7, x_9, x_1, x_10, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Environment_Replay_throwKernelException___redArg(x_14, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_2, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 4);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_st_ref_set(x_2, x_24, x_19);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_addDecl___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_addDecl___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_Replay_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_ConstantInfo_name(x_5);
x_8 = l_Lean_ConstantInfo_type(x_5);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_Lean_ConstantInfo_name(x_11);
x_14 = l_Lean_ConstantInfo_type(x_11);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_reverse___redArg(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_3, 1);
x_11 = l_Lean_instInhabitedConstantInfo;
x_12 = lean_array_get_size(x_10);
x_13 = l_Lean_Name_hash___override(x_8);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_unsigned_to_nat(16u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_sub(x_23, x_25);
x_27 = lean_usize_land(x_22, x_26);
x_28 = lean_array_uget(x_10, x_27);
x_29 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_11, x_8, x_28);
lean_dec(x_28);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_29);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; lean_object* x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = lean_ctor_get(x_3, 1);
x_34 = l_Lean_instInhabitedConstantInfo;
x_35 = lean_array_get_size(x_33);
x_36 = l_Lean_Name_hash___override(x_31);
x_37 = lean_unsigned_to_nat(32u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_xor(x_36, x_39);
x_41 = lean_unsigned_to_nat(16u);
x_42 = lean_uint64_of_nat(x_41);
x_43 = lean_uint64_shift_right(x_40, x_42);
x_44 = lean_uint64_xor(x_40, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_usize_of_nat(x_47);
x_49 = lean_usize_sub(x_46, x_48);
x_50 = lean_usize_land(x_45, x_49);
x_51 = lean_array_uget(x_33, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_34, x_31, x_51);
lean_dec(x_51);
lean_dec(x_31);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_2);
x_1 = x_32;
x_2 = x_53;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___redArg(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_3, 1);
x_12 = l_Lean_instInhabitedConstantInfo;
x_13 = lean_array_get_size(x_11);
x_14 = l_Lean_Name_hash___override(x_9);
x_15 = lean_unsigned_to_nat(32u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_sub(x_24, x_26);
x_28 = lean_usize_land(x_23, x_27);
x_29 = lean_array_uget(x_11, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_12, x_9, x_29);
lean_dec(x_29);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_30);
x_31 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_10, x_1, x_3, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = lean_ctor_get(x_3, 1);
x_35 = l_Lean_instInhabitedConstantInfo;
x_36 = lean_array_get_size(x_34);
x_37 = l_Lean_Name_hash___override(x_32);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_34, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_throwAlreadyImported_spec__0___redArg(x_35, x_32, x_52);
lean_dec(x_52);
lean_dec(x_32);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_2);
x_55 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_33, x_54, x_3, x_5);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_instMonadEIO(lean_box(0));
x_6 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_5);
x_7 = lean_box(0);
x_8 = l_instInhabitedOfMonad___redArg(x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_3(x_10, x_2, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_7);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Environment_Replay_replayConstants(x_9, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_1 = x_8;
x_2 = x_12;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_st_ref_take(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l_Lean_ConstantInfo_name(x_6);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
x_15 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_12, x_11);
x_16 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_12, x_13);
lean_dec(x_12);
x_17 = lean_ctor_get(x_9, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 4);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
x_20 = lean_st_ref_set(x_3, x_19, x_10);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_1 = x_7;
x_2 = x_22;
x_4 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_st_ref_take(x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_Lean_ConstantInfo_name(x_8);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_14, x_13);
x_18 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_14, x_15);
lean_dec(x_14);
x_19 = lean_ctor_get(x_11, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 4);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_st_ref_set(x_5, x_21, x_12);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(x_9, x_24, x_5, x_23);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_reverse___redArg(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_ConstantInfo_inductiveVal_x21(x_9);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_12, x_13, x_3, x_4, x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_4 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_21);
{
lean_object* _tmp_0 = x_10;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_4 = x_20;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_5 = _tmp_4;
}
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = l_Lean_ConstantInfo_inductiveVal_x21(x_23);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_26, x_27, x_3, x_4, x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
x_1 = x_24;
x_2 = x_33;
x_5 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___redArg(x_9, x_10, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_8;
x_2 = x_10;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_ConstantInfo_name(x_7);
x_10 = l_Lean_ConstantInfo_type(x_7);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(x_8, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_13);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_ConstantInfo_name(x_17);
x_20 = l_Lean_ConstantInfo_type(x_17);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__0(x_18, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_1 = x_16;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_inc(x_1);
x_25 = l_Lean_Environment_Replay_isTodo___redArg(x_1, x_3, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_array_get_size(x_35);
x_37 = l_Lean_Name_hash___override(x_1);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_35, x_51);
lean_dec(x_35);
x_53 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_1, x_52);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_54 = lean_mk_string_unchecked("Lean.Replay", 11, 11);
x_55 = lean_mk_string_unchecked("Lean.Environment.Replay.replayConstant", 38, 38);
x_56 = lean_unsigned_to_nat(74u);
x_57 = lean_unsigned_to_nat(50u);
x_58 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_59 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_54, x_55, x_56, x_57, x_58);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
x_60 = l_panic___at___Lean_Environment_Replay_replayConstant_spec__3(x_59, x_2, x_3, x_34);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
lean_dec(x_53);
lean_inc(x_61);
x_62 = l_Lean_ConstantInfo_getUsedConstantsAsSet(x_61);
lean_inc(x_3);
lean_inc(x_2);
x_63 = l_Lean_Environment_Replay_replayConstants(x_62, x_2, x_3, x_34);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_3, x_64);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_67, 2);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_NameSet_contains(x_69, x_1);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_box(0);
lean_ctor_set(x_65, 0, x_71);
return x_65;
}
else
{
lean_free_object(x_65);
switch (lean_obj_tag(x_61)) {
case 0:
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_61);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_5 = x_3;
x_6 = x_74;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_73;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
lean_inc(x_75);
lean_dec(x_61);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_Environment_Replay_addDecl___redArg(x_76, x_3, x_68);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_5 = x_3;
x_6 = x_78;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_77;
}
}
}
case 1:
{
uint8_t x_79; 
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_5 = x_3;
x_6 = x_81;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_80;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_61, 0);
lean_inc(x_82);
lean_dec(x_61);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_Environment_Replay_addDecl___redArg(x_83, x_3, x_68);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_5 = x_3;
x_6 = x_85;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_84;
}
}
}
case 2:
{
uint8_t x_86; 
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_5 = x_3;
x_6 = x_88;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_87;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_61, 0);
lean_inc(x_89);
lean_dec(x_61);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_Environment_Replay_addDecl___redArg(x_90, x_3, x_68);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_5 = x_3;
x_6 = x_92;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_91;
}
}
}
case 3:
{
uint8_t x_93; 
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_61);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = l_Lean_Environment_Replay_addDecl___redArg(x_61, x_3, x_68);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_5 = x_3;
x_6 = x_95;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_94;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_61, 0);
lean_inc(x_96);
lean_dec(x_61);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_Environment_Replay_addDecl___redArg(x_97, x_3, x_68);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_5 = x_3;
x_6 = x_99;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_98;
}
}
}
case 4:
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_61);
lean_dec(x_2);
x_100 = lean_box(4);
x_101 = l_Lean_Environment_Replay_addDecl___redArg(x_100, x_3, x_68);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_5 = x_3;
x_6 = x_102;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_101;
}
}
case 5:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_103 = lean_ctor_get(x_61, 0);
lean_inc(x_103);
lean_dec(x_61);
x_104 = lean_ctor_get(x_103, 3);
lean_inc(x_104);
x_105 = lean_box(0);
x_106 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_104, x_105, x_2, x_3, x_68);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_box(0);
x_110 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_107, x_107, x_109, x_2, x_3, x_108);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
x_113 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(x_107, x_112, x_2, x_3, x_111);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_3);
lean_inc(x_114);
x_116 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(x_114, x_109, x_2, x_3, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get(x_103, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_ctor_get(x_103, 1);
lean_inc(x_120);
lean_dec(x_103);
x_121 = lean_box(0);
x_122 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(x_114, x_121);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_122);
x_125 = lean_unbox(x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*3, x_125);
x_126 = l_Lean_Environment_Replay_addDecl___redArg(x_124, x_3, x_117);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_5 = x_3;
x_6 = x_127;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_126;
}
}
else
{
lean_dec(x_114);
lean_dec(x_103);
lean_dec(x_3);
lean_dec(x_1);
return x_116;
}
}
case 6:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_2);
x_128 = lean_ctor_get(x_61, 0);
lean_inc(x_128);
lean_dec(x_61);
x_129 = lean_st_ref_take(x_3, x_68);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
lean_dec(x_128);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_Lean_NameSet_insert(x_135, x_137);
x_139 = lean_ctor_get(x_130, 4);
lean_inc(x_139);
lean_dec(x_130);
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_132);
lean_ctor_set(x_140, 1, x_133);
lean_ctor_set(x_140, 2, x_134);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_139);
x_141 = lean_st_ref_set(x_3, x_140, x_131);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_5 = x_3;
x_6 = x_142;
goto block_24;
}
default: 
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_2);
x_143 = lean_ctor_get(x_61, 0);
lean_inc(x_143);
lean_dec(x_61);
x_144 = lean_st_ref_take(x_3, x_68);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_145, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 4);
lean_inc(x_151);
lean_dec(x_145);
x_152 = lean_ctor_get(x_143, 0);
lean_inc(x_152);
lean_dec(x_143);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_Lean_NameSet_insert(x_151, x_153);
x_155 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_155, 0, x_147);
lean_ctor_set(x_155, 1, x_148);
lean_ctor_set(x_155, 2, x_149);
lean_ctor_set(x_155, 3, x_150);
lean_ctor_set(x_155, 4, x_154);
x_156 = lean_st_ref_set(x_3, x_155, x_146);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_5 = x_3;
x_6 = x_157;
goto block_24;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_65, 0);
x_159 = lean_ctor_get(x_65, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_65);
x_160 = lean_ctor_get(x_158, 2);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_NameSet_contains(x_160, x_1);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_159);
return x_163;
}
else
{
switch (lean_obj_tag(x_61)) {
case 0:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_2);
x_164 = lean_ctor_get(x_61, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_165 = x_61;
} else {
 lean_dec_ref(x_61);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
x_167 = l_Lean_Environment_Replay_addDecl___redArg(x_166, x_3, x_159);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_5 = x_3;
x_6 = x_168;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_167;
}
}
case 1:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_169 = lean_ctor_get(x_61, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_170 = x_61;
} else {
 lean_dec_ref(x_61);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
x_172 = l_Lean_Environment_Replay_addDecl___redArg(x_171, x_3, x_159);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_5 = x_3;
x_6 = x_173;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_172;
}
}
case 2:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_2);
x_174 = lean_ctor_get(x_61, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_175 = x_61;
} else {
 lean_dec_ref(x_61);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(2, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
x_177 = l_Lean_Environment_Replay_addDecl___redArg(x_176, x_3, x_159);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_5 = x_3;
x_6 = x_178;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_177;
}
}
case 3:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_2);
x_179 = lean_ctor_get(x_61, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_180 = x_61;
} else {
 lean_dec_ref(x_61);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(3, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
x_182 = l_Lean_Environment_Replay_addDecl___redArg(x_181, x_3, x_159);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_5 = x_3;
x_6 = x_183;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_182;
}
}
case 4:
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_61);
lean_dec(x_2);
x_184 = lean_box(4);
x_185 = l_Lean_Environment_Replay_addDecl___redArg(x_184, x_3, x_159);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_5 = x_3;
x_6 = x_186;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_185;
}
}
case 5:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_187 = lean_ctor_get(x_61, 0);
lean_inc(x_187);
lean_dec(x_61);
x_188 = lean_ctor_get(x_187, 3);
lean_inc(x_188);
x_189 = lean_box(0);
x_190 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_188, x_189, x_2, x_3, x_159);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_box(0);
x_194 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_191, x_191, x_193, x_2, x_3, x_192);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_box(0);
x_197 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(x_191, x_196, x_2, x_3, x_195);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
lean_inc(x_3);
lean_inc(x_198);
x_200 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___redArg(x_198, x_193, x_2, x_3, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_ctor_get(x_187, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_ctor_get(x_187, 1);
lean_inc(x_204);
lean_dec(x_187);
x_205 = lean_box(0);
x_206 = l_List_mapTR_loop___at___Lean_Environment_Replay_replayConstant_spec__9(x_198, x_205);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_208, 0, x_203);
lean_ctor_set(x_208, 1, x_204);
lean_ctor_set(x_208, 2, x_206);
x_209 = lean_unbox(x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*3, x_209);
x_210 = l_Lean_Environment_Replay_addDecl___redArg(x_208, x_3, x_201);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_5 = x_3;
x_6 = x_211;
goto block_24;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_210;
}
}
else
{
lean_dec(x_198);
lean_dec(x_187);
lean_dec(x_3);
lean_dec(x_1);
return x_200;
}
}
case 6:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_2);
x_212 = lean_ctor_get(x_61, 0);
lean_inc(x_212);
lean_dec(x_61);
x_213 = lean_st_ref_take(x_3, x_159);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_214, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_212, 0);
lean_inc(x_220);
lean_dec(x_212);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_NameSet_insert(x_219, x_221);
x_223 = lean_ctor_get(x_214, 4);
lean_inc(x_223);
lean_dec(x_214);
x_224 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_224, 0, x_216);
lean_ctor_set(x_224, 1, x_217);
lean_ctor_set(x_224, 2, x_218);
lean_ctor_set(x_224, 3, x_222);
lean_ctor_set(x_224, 4, x_223);
x_225 = lean_st_ref_set(x_3, x_224, x_215);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_5 = x_3;
x_6 = x_226;
goto block_24;
}
default: 
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_2);
x_227 = lean_ctor_get(x_61, 0);
lean_inc(x_227);
lean_dec(x_61);
x_228 = lean_st_ref_take(x_3, x_159);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_229, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_229, 3);
lean_inc(x_234);
x_235 = lean_ctor_get(x_229, 4);
lean_inc(x_235);
lean_dec(x_229);
x_236 = lean_ctor_get(x_227, 0);
lean_inc(x_236);
lean_dec(x_227);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec(x_236);
x_238 = l_Lean_NameSet_insert(x_235, x_237);
x_239 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_232);
lean_ctor_set(x_239, 2, x_233);
lean_ctor_set(x_239, 3, x_234);
lean_ctor_set(x_239, 4, x_238);
x_240 = lean_st_ref_set(x_3, x_239, x_230);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_5 = x_3;
x_6 = x_241;
goto block_24;
}
}
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_63;
}
}
}
block_24:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = l_Lean_RBNode_erase___at___Lean_Environment_Replay_isTodo_spec__0___redArg(x_1, x_10);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
x_17 = lean_st_ref_set(x_5, x_16, x_9);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Environment_Replay_replayConstant(x_9, x_3, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_1 = x_10;
x_2 = x_16;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_replayConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Environment_Replay_replayConstant_spec__3___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM_loop___at___Lean_Environment_Replay_replayConstant_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___Lean_Environment_Replay_replayConstant_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_16 = lean_st_ref_get(x_4, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 1, 0);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_9);
x_32 = l_Lean_Environment_find_x3f(x_29, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 6)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_3, 1);
x_36 = lean_array_get_size(x_35);
x_37 = l_Lean_Name_hash___override(x_9);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_35, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_9, x_52);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec(x_34);
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 6)
{
uint8_t x_55; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3023_(x_34, x_56);
lean_dec(x_56);
lean_dec(x_34);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
x_58 = lean_box(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = lean_box(1);
x_61 = lean_mk_string_unchecked("Invalid constructor ", 20, 20);
x_62 = lean_unbox(x_60);
x_63 = l_Lean_Name_toString(x_9, x_62, x_59);
x_64 = lean_string_append(x_61, x_63);
lean_dec(x_63);
lean_ctor_set_tag(x_54, 18);
lean_ctor_set(x_54, 0, x_64);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_54);
return x_11;
}
else
{
lean_object* x_65; 
lean_free_object(x_54);
lean_free_object(x_11);
lean_dec(x_9);
x_65 = lean_box(0);
x_1 = x_10;
x_2 = x_65;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
lean_dec(x_54);
x_68 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3023_(x_34, x_67);
lean_dec(x_67);
lean_dec(x_34);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_10);
x_69 = lean_box(x_68);
x_70 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_70, 0, x_69);
x_71 = lean_box(1);
x_72 = lean_mk_string_unchecked("Invalid constructor ", 20, 20);
x_73 = lean_unbox(x_71);
x_74 = l_Lean_Name_toString(x_9, x_73, x_70);
x_75 = lean_string_append(x_72, x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_76);
return x_11;
}
else
{
lean_object* x_77; 
lean_free_object(x_11);
lean_dec(x_9);
x_77 = lean_box(0);
x_1 = x_10;
x_2 = x_77;
x_5 = x_18;
goto _start;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_34);
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
}
}
else
{
lean_dec(x_33);
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
}
block_28:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_mk_string_unchecked("No such constructor ", 20, 20);
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Name_toString(x_9, x_23, x_20);
x_25 = lean_string_append(x_21, x_24);
lean_dec(x_24);
if (lean_is_scalar(x_15)) {
 x_26 = lean_alloc_ctor(18, 1, 0);
} else {
 x_26 = x_15;
 lean_ctor_set_tag(x_26, 18);
}
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_19)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_19;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_11, 0);
x_80 = lean_ctor_get(x_11, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_11);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_st_ref_get(x_4, x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 1, 0);
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
lean_dec(x_83);
x_96 = lean_box(0);
x_97 = lean_unbox(x_96);
lean_inc(x_9);
x_98 = l_Lean_Environment_find_x3f(x_95, x_9, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_dec(x_10);
goto block_94;
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 6)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; size_t x_112; size_t x_113; lean_object* x_114; size_t x_115; size_t x_116; size_t x_117; lean_object* x_118; lean_object* x_119; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_3, 1);
x_102 = lean_array_get_size(x_101);
x_103 = l_Lean_Name_hash___override(x_9);
x_104 = lean_unsigned_to_nat(32u);
x_105 = lean_uint64_of_nat(x_104);
x_106 = lean_uint64_shift_right(x_103, x_105);
x_107 = lean_uint64_xor(x_103, x_106);
x_108 = lean_unsigned_to_nat(16u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_uint64_to_usize(x_111);
x_113 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_usize_of_nat(x_114);
x_116 = lean_usize_sub(x_113, x_115);
x_117 = lean_usize_land(x_112, x_116);
x_118 = lean_array_uget(x_101, x_117);
x_119 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_9, x_118);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_dec(x_100);
lean_dec(x_10);
goto block_94;
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 6)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_81);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = l___private_Lean_Declaration_0__Lean_beqConstructorVal____x40_Lean_Declaration___hyg_3023_(x_100, x_121);
lean_dec(x_121);
lean_dec(x_100);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_10);
x_124 = lean_box(x_123);
x_125 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_125, 0, x_124);
x_126 = lean_box(1);
x_127 = lean_mk_string_unchecked("Invalid constructor ", 20, 20);
x_128 = lean_unbox(x_126);
x_129 = l_Lean_Name_toString(x_9, x_128, x_125);
x_130 = lean_string_append(x_127, x_129);
lean_dec(x_129);
if (lean_is_scalar(x_122)) {
 x_131 = lean_alloc_ctor(18, 1, 0);
} else {
 x_131 = x_122;
 lean_ctor_set_tag(x_131, 18);
}
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_84);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_122);
lean_dec(x_9);
x_133 = lean_box(0);
x_1 = x_10;
x_2 = x_133;
x_5 = x_84;
goto _start;
}
}
else
{
lean_dec(x_120);
lean_dec(x_100);
lean_dec(x_10);
goto block_94;
}
}
}
else
{
lean_dec(x_99);
lean_dec(x_10);
goto block_94;
}
}
block_94:
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_mk_string_unchecked("No such constructor ", 20, 20);
x_88 = lean_box(1);
x_89 = lean_unbox(x_88);
x_90 = l_Lean_Name_toString(x_9, x_89, x_86);
x_91 = lean_string_append(x_87, x_90);
lean_dec(x_90);
if (lean_is_scalar(x_81)) {
 x_92 = lean_alloc_ctor(18, 1, 0);
} else {
 x_92 = x_81;
 lean_ctor_set_tag(x_92, 18);
}
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_85;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_84);
return x_93;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(x_7, x_8, x_1, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedConstructors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_16 = lean_st_ref_get(x_4, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 1, 0);
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_9);
x_32 = l_Lean_Environment_find_x3f(x_29, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 7)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_3, 1);
x_36 = lean_array_get_size(x_35);
x_37 = l_Lean_Name_hash___override(x_9);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_uint64_of_nat(x_38);
x_40 = lean_uint64_shift_right(x_37, x_39);
x_41 = lean_uint64_xor(x_37, x_40);
x_42 = lean_unsigned_to_nat(16u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_usize_sub(x_47, x_49);
x_51 = lean_usize_land(x_46, x_50);
x_52 = lean_array_uget(x_35, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_9, x_52);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec(x_34);
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 7)
{
uint8_t x_55; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3455_(x_34, x_56);
lean_dec(x_56);
lean_dec(x_34);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
x_58 = lean_box(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = lean_box(1);
x_61 = lean_mk_string_unchecked("Invalid recursor ", 17, 17);
x_62 = lean_unbox(x_60);
x_63 = l_Lean_Name_toString(x_9, x_62, x_59);
x_64 = lean_string_append(x_61, x_63);
lean_dec(x_63);
lean_ctor_set_tag(x_54, 18);
lean_ctor_set(x_54, 0, x_64);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_54);
return x_11;
}
else
{
lean_object* x_65; 
lean_free_object(x_54);
lean_free_object(x_11);
lean_dec(x_9);
x_65 = lean_box(0);
x_1 = x_10;
x_2 = x_65;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
lean_dec(x_54);
x_68 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3455_(x_34, x_67);
lean_dec(x_67);
lean_dec(x_34);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_10);
x_69 = lean_box(x_68);
x_70 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_70, 0, x_69);
x_71 = lean_box(1);
x_72 = lean_mk_string_unchecked("Invalid recursor ", 17, 17);
x_73 = lean_unbox(x_71);
x_74 = l_Lean_Name_toString(x_9, x_73, x_70);
x_75 = lean_string_append(x_72, x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_76);
return x_11;
}
else
{
lean_object* x_77; 
lean_free_object(x_11);
lean_dec(x_9);
x_77 = lean_box(0);
x_1 = x_10;
x_2 = x_77;
x_5 = x_18;
goto _start;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_34);
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
}
}
else
{
lean_dec(x_33);
lean_free_object(x_11);
lean_dec(x_10);
goto block_28;
}
}
block_28:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_mk_string_unchecked("No such recursor ", 17, 17);
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Name_toString(x_9, x_23, x_20);
x_25 = lean_string_append(x_21, x_24);
lean_dec(x_24);
if (lean_is_scalar(x_15)) {
 x_26 = lean_alloc_ctor(18, 1, 0);
} else {
 x_26 = x_15;
 lean_ctor_set_tag(x_26, 18);
}
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_19)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_19;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_11, 0);
x_80 = lean_ctor_get(x_11, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_11);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_st_ref_get(x_4, x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__0___boxed), 1, 0);
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
lean_dec(x_83);
x_96 = lean_box(0);
x_97 = lean_unbox(x_96);
lean_inc(x_9);
x_98 = l_Lean_Environment_find_x3f(x_95, x_9, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_dec(x_10);
goto block_94;
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 7)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; size_t x_112; size_t x_113; lean_object* x_114; size_t x_115; size_t x_116; size_t x_117; lean_object* x_118; lean_object* x_119; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_3, 1);
x_102 = lean_array_get_size(x_101);
x_103 = l_Lean_Name_hash___override(x_9);
x_104 = lean_unsigned_to_nat(32u);
x_105 = lean_uint64_of_nat(x_104);
x_106 = lean_uint64_shift_right(x_103, x_105);
x_107 = lean_uint64_xor(x_103, x_106);
x_108 = lean_unsigned_to_nat(16u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_uint64_to_usize(x_111);
x_113 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_usize_of_nat(x_114);
x_116 = lean_usize_sub(x_113, x_115);
x_117 = lean_usize_land(x_112, x_116);
x_118 = lean_array_uget(x_101, x_117);
x_119 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_9, x_118);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_dec(x_100);
lean_dec(x_10);
goto block_94;
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 7)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_81);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = l___private_Lean_Declaration_0__Lean_beqRecursorVal____x40_Lean_Declaration___hyg_3455_(x_100, x_121);
lean_dec(x_121);
lean_dec(x_100);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_10);
x_124 = lean_box(x_123);
x_125 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedConstructors_spec__0___lam__1___boxed), 2, 1);
lean_closure_set(x_125, 0, x_124);
x_126 = lean_box(1);
x_127 = lean_mk_string_unchecked("Invalid recursor ", 17, 17);
x_128 = lean_unbox(x_126);
x_129 = l_Lean_Name_toString(x_9, x_128, x_125);
x_130 = lean_string_append(x_127, x_129);
lean_dec(x_129);
if (lean_is_scalar(x_122)) {
 x_131 = lean_alloc_ctor(18, 1, 0);
} else {
 x_131 = x_122;
 lean_ctor_set_tag(x_131, 18);
}
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_84);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_122);
lean_dec(x_9);
x_133 = lean_box(0);
x_1 = x_10;
x_2 = x_133;
x_5 = x_84;
goto _start;
}
}
else
{
lean_dec(x_120);
lean_dec(x_100);
lean_dec(x_10);
goto block_94;
}
}
}
else
{
lean_dec(x_99);
lean_dec(x_10);
goto block_94;
}
}
block_94:
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_mk_string_unchecked("No such recursor ", 17, 17);
x_88 = lean_box(1);
x_89 = lean_unbox(x_88);
x_90 = l_Lean_Name_toString(x_9, x_89, x_86);
x_91 = lean_string_append(x_87, x_90);
lean_dec(x_90);
if (lean_is_scalar(x_81)) {
 x_92 = lean_alloc_ctor(18, 1, 0);
} else {
 x_92 = x_81;
 lean_ctor_set_tag(x_92, 18);
}
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_85;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_84);
return x_93;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 4);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(x_7, x_8, x_1, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_checkPostponedRecursors_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_Replay_checkPostponedRecursors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_ConstantInfo_isUnsafe(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_ConstantInfo_isPartial(x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_NameSet_insert(x_2, x_7);
x_1 = x_6;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
x_1 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(x_1, x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_replay(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_20; lean_object* x_21; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_20 = lean_box(0);
x_40 = lean_box(0);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_array_get_size(x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
x_21 = x_40;
goto block_39;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_46 = lean_usize_of_nat(x_43);
x_47 = l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(x_41, x_45, x_46, x_40);
lean_dec(x_41);
x_21 = x_47;
goto block_39;
}
block_19:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_4, x_6);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
block_39:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___redArg(x_21, x_20, x_3);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_20);
x_26 = lean_st_mk_ref(x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
lean_inc(x_27);
lean_inc(x_1);
x_30 = l_Lean_RBNode_forIn_visit___at___Lean_Environment_Replay_replayConstants_spec__0(x_23, x_29, x_1, x_27, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Environment_Replay_checkPostponedConstructors(x_1, x_27, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Environment_Replay_checkPostponedRecursors(x_1, x_27, x_33);
lean_dec(x_1);
x_4 = x_27;
x_5 = x_34;
goto block_19;
}
else
{
lean_dec(x_1);
x_4 = x_27;
x_5 = x_32;
goto block_19;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_Environment_replay_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Environment_replay_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Environment_replay_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Replay(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
