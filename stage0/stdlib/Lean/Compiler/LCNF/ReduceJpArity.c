// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceJpArity
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.PassManager
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_3, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_array_uget(x_1, x_3);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_21, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Compiler_LCNF_eraseParam(x_19, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_array_push(x_22, x_30);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 0, x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_10 = x_32;
x_11 = x_28;
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_box(0);
x_35 = lean_array_push(x_22, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_21);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_10 = x_37;
x_11 = x_33;
goto block_16;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_38, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_19, 2);
lean_inc(x_42);
x_43 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_42, x_21);
x_44 = lean_box(x_17);
x_45 = lean_array_push(x_22, x_44);
x_46 = lean_array_push(x_23, x_19);
lean_ctor_set(x_38, 1, x_43);
lean_ctor_set(x_38, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_38);
x_10 = x_47;
x_11 = x_9;
goto block_16;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_38);
x_48 = lean_ctor_get(x_19, 2);
lean_inc(x_48);
x_49 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_48, x_21);
x_50 = lean_box(x_17);
x_51 = lean_array_push(x_22, x_50);
x_52 = lean_array_push(x_23, x_19);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_10 = x_54;
x_11 = x_9;
goto block_16;
}
}
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget(x_1, x_3);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_17, x_25);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_18);
if (x_23 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_6 = x_28;
x_7 = x_5;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_24, x_17);
lean_dec(x_17);
lean_dec(x_24);
x_30 = lean_array_push(x_16, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_6 = x_31;
x_7 = x_5;
goto block_12;
}
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
x_13 = x_33;
goto block_32;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
x_13 = x_34;
goto block_32;
}
block_32:
{
lean_object* x_14; 
lean_inc(x_3);
x_14 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_12, x_15);
x_18 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = lean_array_fset(x_2, x_1, x_17);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_23;
x_8 = x_16;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
lean_dec(x_1);
x_1 = x_26;
x_8 = x_16;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; size_t x_23; size_t x_24; uint8_t x_25; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
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
x_23 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_24 = lean_ptr_addr(x_11);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
x_14 = x_25;
goto block_22;
}
else
{
size_t x_26; uint8_t x_27; 
x_26 = lean_ptr_addr(x_8);
x_27 = lean_usize_dec_eq(x_26, x_26);
x_14 = x_27;
goto block_22;
}
block_22:
{
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_11);
if (lean_is_scalar(x_13)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_13;
}
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
if (lean_is_scalar(x_13)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_13;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_8);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 4);
lean_inc(x_30);
lean_inc(x_2);
x_31 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_30, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_28, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 2);
lean_inc(x_35);
lean_inc(x_28);
x_36 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_28, x_34, x_35, x_32, x_4, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_29);
x_39 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_29, x_2, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; size_t x_52; size_t x_53; uint8_t x_54; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_52 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_53 = lean_ptr_addr(x_40);
x_54 = lean_usize_dec_eq(x_52, x_53);
if (x_54 == 0)
{
lean_dec(x_28);
x_43 = x_54;
goto block_51;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; 
x_55 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_56 = lean_ptr_addr(x_37);
x_57 = lean_usize_dec_eq(x_55, x_56);
x_43 = x_57;
goto block_51;
}
block_51:
{
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_1, 0);
lean_dec(x_46);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_37);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_40);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_40);
lean_dec(x_37);
if (lean_is_scalar(x_42)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_42;
}
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_1);
return x_39;
}
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 4);
lean_inc(x_60);
lean_inc(x_2);
x_61 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_60, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = lean_box(0);
lean_inc(x_63);
x_66 = l_Lean_Compiler_LCNF_Code_collectUsed(x_63, x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_mk_empty_array_with_capacity(x_67);
x_69 = lean_ctor_get(x_58, 2);
lean_inc(x_69);
lean_inc(x_69);
x_70 = l_Array_reverse(lean_box(0), x_69);
lean_inc(x_68);
lean_ctor_set(x_61, 1, x_66);
lean_ctor_set(x_61, 0, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_61);
x_72 = lean_array_size(x_70);
x_73 = lean_usize_of_nat(x_67);
x_74 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_70, x_72, x_73, x_71, x_3, x_4, x_5, x_6, x_64);
lean_dec(x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l_Array_reverse(lean_box(0), x_79);
x_81 = lean_array_get_size(x_80);
x_82 = lean_array_get_size(x_69);
x_83 = lean_nat_dec_eq(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_69);
x_84 = !lean_is_exclusive(x_1);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_1, 0);
lean_dec(x_86);
lean_inc(x_63);
x_87 = l_Lean_Compiler_LCNF_Code_inferType(x_63, x_3, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_80);
x_90 = l_Lean_Compiler_LCNF_mkForallParams(x_80, x_88, x_3, x_4, x_5, x_6, x_89);
lean_dec(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_91, x_80, x_63, x_4, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Array_reverse(lean_box(0), x_78);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
x_98 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_97, x_96);
x_99 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_98, x_3, x_4, x_5, x_6, x_95);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_ctor_set(x_1, 1, x_101);
lean_ctor_set(x_1, 0, x_94);
lean_ctor_set(x_99, 0, x_1);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_99);
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_94);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_dec(x_94);
lean_free_object(x_1);
return x_99;
}
}
else
{
uint8_t x_105; 
lean_free_object(x_1);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_90);
if (x_105 == 0)
{
return x_90;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_90, 0);
x_107 = lean_ctor_get(x_90, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_90);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_free_object(x_1);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_87);
if (x_109 == 0)
{
return x_87;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_87, 0);
x_111 = lean_ctor_get(x_87, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_87);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_1);
lean_inc(x_63);
x_113 = l_Lean_Compiler_LCNF_Code_inferType(x_63, x_3, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_80);
x_116 = l_Lean_Compiler_LCNF_mkForallParams(x_80, x_114, x_3, x_4, x_5, x_6, x_115);
lean_dec(x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_117, x_80, x_63, x_4, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Array_reverse(lean_box(0), x_78);
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_123, x_122);
x_125 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_124, x_3, x_4, x_5, x_6, x_121);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set(x_129, 1, x_126);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
else
{
lean_dec(x_120);
return x_125;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_135 = lean_ctor_get(x_113, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_113, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_137 = x_113;
} else {
 lean_dec_ref(x_113);
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
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_80);
lean_dec(x_78);
x_139 = lean_ctor_get(x_58, 3);
lean_inc(x_139);
lean_inc(x_58);
x_140 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_139, x_69, x_63, x_4, x_77);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_59);
x_143 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_2, x_3, x_4, x_5, x_6, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; size_t x_163; size_t x_164; uint8_t x_165; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_163 = lean_ptr_addr(x_59);
lean_dec(x_59);
x_164 = lean_ptr_addr(x_144);
x_165 = lean_usize_dec_eq(x_163, x_164);
if (x_165 == 0)
{
lean_dec(x_58);
x_147 = x_165;
goto block_162;
}
else
{
size_t x_166; size_t x_167; uint8_t x_168; 
x_166 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_167 = lean_ptr_addr(x_141);
x_168 = lean_usize_dec_eq(x_166, x_167);
x_147 = x_168;
goto block_162;
}
block_162:
{
if (x_147 == 0)
{
if (x_83 == 0)
{
lean_object* x_148; 
lean_dec(x_144);
lean_dec(x_141);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_1);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_1, 1);
lean_dec(x_150);
x_151 = lean_ctor_get(x_1, 0);
lean_dec(x_151);
lean_ctor_set(x_1, 1, x_144);
lean_ctor_set(x_1, 0, x_141);
if (lean_is_scalar(x_146)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_146;
}
lean_ctor_set(x_152, 0, x_1);
lean_ctor_set(x_152, 1, x_145);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_1);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_141);
lean_ctor_set(x_153, 1, x_144);
if (lean_is_scalar(x_146)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_146;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_145);
return x_154;
}
}
}
else
{
if (x_83 == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_1);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_1, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_1, 0);
lean_dec(x_157);
lean_ctor_set(x_1, 1, x_144);
lean_ctor_set(x_1, 0, x_141);
if (lean_is_scalar(x_146)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_146;
}
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_145);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_1);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_141);
lean_ctor_set(x_159, 1, x_144);
if (lean_is_scalar(x_146)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_146;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_145);
return x_160;
}
}
else
{
lean_object* x_161; 
lean_dec(x_144);
lean_dec(x_141);
if (lean_is_scalar(x_146)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_146;
}
lean_ctor_set(x_161, 0, x_1);
lean_ctor_set(x_161, 1, x_145);
return x_161;
}
}
}
}
else
{
lean_dec(x_141);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
return x_143;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; size_t x_179; size_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_169 = lean_ctor_get(x_61, 0);
x_170 = lean_ctor_get(x_61, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_61);
x_171 = lean_box(0);
lean_inc(x_169);
x_172 = l_Lean_Compiler_LCNF_Code_collectUsed(x_169, x_171);
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_mk_empty_array_with_capacity(x_173);
x_175 = lean_ctor_get(x_58, 2);
lean_inc(x_175);
lean_inc(x_175);
x_176 = l_Array_reverse(lean_box(0), x_175);
lean_inc(x_174);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_172);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_array_size(x_176);
x_180 = lean_usize_of_nat(x_173);
x_181 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_176, x_179, x_180, x_178, x_3, x_4, x_5, x_6, x_170);
lean_dec(x_176);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec(x_183);
x_187 = l_Array_reverse(lean_box(0), x_186);
x_188 = lean_array_get_size(x_187);
x_189 = lean_array_get_size(x_175);
x_190 = lean_nat_dec_eq(x_188, x_189);
lean_dec(x_189);
lean_dec(x_188);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_175);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_191 = x_1;
} else {
 lean_dec_ref(x_1);
 x_191 = lean_box(0);
}
lean_inc(x_169);
x_192 = l_Lean_Compiler_LCNF_Code_inferType(x_169, x_3, x_4, x_5, x_6, x_184);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_187);
x_195 = l_Lean_Compiler_LCNF_mkForallParams(x_187, x_193, x_3, x_4, x_5, x_6, x_194);
lean_dec(x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_196, x_187, x_169, x_4, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Array_reverse(lean_box(0), x_185);
x_202 = lean_ctor_get(x_199, 0);
lean_inc(x_202);
x_203 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_2, x_202, x_201);
x_204 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_203, x_3, x_4, x_5, x_6, x_200);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_208 = lean_alloc_ctor(2, 2, 0);
} else {
 x_208 = x_191;
}
lean_ctor_set(x_208, 0, x_199);
lean_ctor_set(x_208, 1, x_205);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_206);
return x_209;
}
else
{
lean_dec(x_199);
lean_dec(x_191);
return x_204;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_191);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_169);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_210 = lean_ctor_get(x_195, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_195, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_212 = x_195;
} else {
 lean_dec_ref(x_195);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_191);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_169);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
x_214 = lean_ctor_get(x_192, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_192, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_216 = x_192;
} else {
 lean_dec_ref(x_192);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_187);
lean_dec(x_185);
x_218 = lean_ctor_get(x_58, 3);
lean_inc(x_218);
lean_inc(x_58);
x_219 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_58, x_218, x_175, x_169, x_4, x_184);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_59);
x_222 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_59, x_2, x_3, x_4, x_5, x_6, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; size_t x_236; size_t x_237; uint8_t x_238; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_236 = lean_ptr_addr(x_59);
lean_dec(x_59);
x_237 = lean_ptr_addr(x_223);
x_238 = lean_usize_dec_eq(x_236, x_237);
if (x_238 == 0)
{
lean_dec(x_58);
x_226 = x_238;
goto block_235;
}
else
{
size_t x_239; size_t x_240; uint8_t x_241; 
x_239 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_240 = lean_ptr_addr(x_220);
x_241 = lean_usize_dec_eq(x_239, x_240);
x_226 = x_241;
goto block_235;
}
block_235:
{
if (x_226 == 0)
{
if (x_190 == 0)
{
lean_object* x_227; 
lean_dec(x_223);
lean_dec(x_220);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_1);
lean_ctor_set(x_227, 1, x_224);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_228 = x_1;
} else {
 lean_dec_ref(x_1);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(2, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_220);
lean_ctor_set(x_229, 1, x_223);
if (lean_is_scalar(x_225)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_225;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_224);
return x_230;
}
}
else
{
if (x_190 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_231 = x_1;
} else {
 lean_dec_ref(x_1);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(2, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_220);
lean_ctor_set(x_232, 1, x_223);
if (lean_is_scalar(x_225)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_225;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_224);
return x_233;
}
else
{
lean_object* x_234; 
lean_dec(x_223);
lean_dec(x_220);
if (lean_is_scalar(x_225)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_225;
}
lean_ctor_set(x_234, 0, x_1);
lean_ctor_set(x_234, 1, x_224);
return x_234;
}
}
}
}
else
{
lean_dec(x_220);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
return x_222;
}
}
}
}
else
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_2);
lean_dec(x_1);
return x_61;
}
}
case 3:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_1, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_1, 1);
lean_inc(x_243);
x_244 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(x_2, x_242);
lean_dec(x_2);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
lean_dec(x_243);
lean_dec(x_242);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_1);
lean_ctor_set(x_245, 1, x_7);
return x_245;
}
else
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_1);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; size_t x_255; size_t x_256; lean_object* x_257; uint8_t x_258; 
x_247 = lean_ctor_get(x_1, 1);
lean_dec(x_247);
x_248 = lean_ctor_get(x_1, 0);
lean_dec(x_248);
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
lean_dec(x_244);
x_250 = lean_unsigned_to_nat(0u);
x_251 = lean_mk_empty_array_with_capacity(x_250);
x_252 = lean_array_get_size(x_243);
x_253 = l_Array_toSubarray___redArg(x_243, x_250, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
x_255 = lean_array_size(x_249);
x_256 = lean_usize_of_nat(x_250);
x_257 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_249, x_255, x_256, x_254, x_7);
lean_dec(x_249);
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_257, 0);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_257, 0, x_1);
return x_257;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_257, 0);
x_262 = lean_ctor_get(x_257, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_257);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
lean_ctor_set(x_1, 1, x_263);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_1);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; size_t x_271; size_t x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_1);
x_265 = lean_ctor_get(x_244, 0);
lean_inc(x_265);
lean_dec(x_244);
x_266 = lean_unsigned_to_nat(0u);
x_267 = lean_mk_empty_array_with_capacity(x_266);
x_268 = lean_array_get_size(x_243);
x_269 = l_Array_toSubarray___redArg(x_243, x_266, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
x_271 = lean_array_size(x_265);
x_272 = lean_usize_of_nat(x_266);
x_273 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_265, x_271, x_272, x_270, x_7);
lean_dec(x_265);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
lean_dec(x_274);
x_278 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_278, 0, x_242);
lean_ctor_set(x_278, 1, x_277);
if (lean_is_scalar(x_276)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_276;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_275);
return x_279;
}
}
}
case 4:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = lean_ctor_get(x_1, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 3);
lean_inc(x_281);
x_282 = lean_unsigned_to_nat(0u);
lean_inc(x_281);
x_283 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(x_282, x_281, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_283) == 0)
{
uint8_t x_284; 
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; size_t x_286; size_t x_287; uint8_t x_288; 
x_285 = lean_ctor_get(x_283, 0);
x_286 = lean_ptr_addr(x_281);
lean_dec(x_281);
x_287 = lean_ptr_addr(x_285);
x_288 = lean_usize_dec_eq(x_286, x_287);
if (x_288 == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_1);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_1, 0);
lean_dec(x_290);
x_291 = lean_ctor_get(x_280, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_280, 1);
lean_inc(x_292);
x_293 = lean_ctor_get(x_280, 2);
lean_inc(x_293);
lean_dec(x_280);
x_294 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
lean_ctor_set(x_294, 2, x_293);
lean_ctor_set(x_294, 3, x_285);
lean_ctor_set(x_1, 0, x_294);
lean_ctor_set(x_283, 0, x_1);
return x_283;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_1);
x_295 = lean_ctor_get(x_280, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_280, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_280, 2);
lean_inc(x_297);
lean_dec(x_280);
x_298 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
lean_ctor_set(x_298, 2, x_297);
lean_ctor_set(x_298, 3, x_285);
x_299 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_283, 0, x_299);
return x_283;
}
}
else
{
lean_dec(x_285);
lean_dec(x_280);
lean_ctor_set(x_283, 0, x_1);
return x_283;
}
}
else
{
lean_object* x_300; lean_object* x_301; size_t x_302; size_t x_303; uint8_t x_304; 
x_300 = lean_ctor_get(x_283, 0);
x_301 = lean_ctor_get(x_283, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_283);
x_302 = lean_ptr_addr(x_281);
lean_dec(x_281);
x_303 = lean_ptr_addr(x_300);
x_304 = lean_usize_dec_eq(x_302, x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_305 = x_1;
} else {
 lean_dec_ref(x_1);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_280, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_280, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_280, 2);
lean_inc(x_308);
lean_dec(x_280);
x_309 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
lean_ctor_set(x_309, 2, x_308);
lean_ctor_set(x_309, 3, x_300);
if (lean_is_scalar(x_305)) {
 x_310 = lean_alloc_ctor(4, 1, 0);
} else {
 x_310 = x_305;
}
lean_ctor_set(x_310, 0, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_301);
return x_311;
}
else
{
lean_object* x_312; 
lean_dec(x_300);
lean_dec(x_280);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_1);
lean_ctor_set(x_312, 1, x_301);
return x_312;
}
}
}
else
{
uint8_t x_313; 
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_283);
if (x_313 == 0)
{
return x_283;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_283, 0);
x_315 = lean_ctor_get(x_283, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_283);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
default: 
{
lean_object* x_317; 
lean_dec(x_2);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_1);
lean_ctor_set(x_317, 1, x_7);
return x_317;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceJpArity_reduce_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ReduceJpArity_reduce(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ReduceJpArity_reduce___boxed), 7, 0);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceJpArity_spec__0(x_7, x_8, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_12);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*6 + 1, x_18);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_29 = lean_ctor_get(x_1, 5);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_21);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*6 + 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("reduceJpArity", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceJpArity), 6, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_3, x_4, x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceJpArity___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_LCNF_reduceJpArity(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("reduceJpArity", 13, 13);
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
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("ReduceJpArity", 13, 13);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(879u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceJpArity___hyg_879_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
