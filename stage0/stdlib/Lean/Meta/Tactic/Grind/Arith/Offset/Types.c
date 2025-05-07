// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Offset.Types
// Imports: Lean.Data.AssocList Lean.Data.PersistentArray Lean.Meta.Tactic.Grind.ENodeKey Lean.Meta.Tactic.Grind.Arith.Util Lean.Meta.Tactic.Grind.Arith.Offset.Util
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedToPropagate;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId___lam__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId___lam__0(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedProofInfo;
lean_object* l_Lean_Meta_Grind_Arith_Offset_toMessageData___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("#", 1, 1);
x_3 = l_Lean_stringToMessageData(x_2);
lean_dec(x_2);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_MessageData_ofFormat(x_5);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("", 0, 0);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Offset_toMessageData___redArg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedProofInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedToPropagate() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 4, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = l_Array_empty(lean_box(0));
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
lean_inc(x_1);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set_usize(x_6, 4, x_5);
x_7 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_3);
lean_ctor_set_usize(x_12, 4, x_5);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set_usize(x_14, 4, x_5);
x_15 = lean_box(0);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_10);
lean_ctor_set(x_16, 4, x_12);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_14);
lean_ctor_set(x_16, 7, x_15);
return x_16;
}
}
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_ENodeKey(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_AssocList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ENodeKey(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId = _init_l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_instToMessageDataCnstrNodeId);
l_Lean_Meta_Grind_Arith_Offset_instInhabitedProofInfo = _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedProofInfo();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_instInhabitedProofInfo);
l_Lean_Meta_Grind_Arith_Offset_instInhabitedToPropagate = _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedToPropagate();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_instInhabitedToPropagate);
l_Lean_Meta_Grind_Arith_Offset_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_Offset_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
