// Lean compiler output
// Module: Lean.Compiler.LCNF.ElimDead
// Imports: Lean.Compiler.LCNF.CompilerM
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instBEqFVarId;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableFVarId;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instFVarIdHashSetInhabited;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_collectLocalDeclsType_go_spec__0(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_collectLocalDeclsType_go_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instFVarIdHashSetInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_3);
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
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_3, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
lean_inc(x_3);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_22);
x_30 = lean_array_uset(x_5, x_21, x_29);
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
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_30);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
lean_inc(x_3);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_22);
x_41 = lean_array_uset(x_5, x_21, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_shiftl(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
}
case 5:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
x_53 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_52);
x_1 = x_53;
x_2 = x_51;
goto _start;
}
case 6:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_2, 2);
x_2 = x_55;
goto _start;
}
case 8:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_57 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ElimDead", 27, 27);
x_58 = lean_mk_string_unchecked("Lean.Compiler.LCNF.collectLocalDeclsType.go", 43, 43);
x_59 = lean_unsigned_to_nat(26u);
x_60 = lean_unsigned_to_nat(41u);
x_61 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_62 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_57, x_58, x_59, x_60, x_61);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
x_63 = l_panic___at___Lean_Compiler_LCNF_collectLocalDeclsType_go_spec__0(x_62);
return x_63;
}
case 10:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_64 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ElimDead", 27, 27);
x_65 = lean_mk_string_unchecked("Lean.Compiler.LCNF.collectLocalDeclsType.go", 43, 43);
x_66 = lean_unsigned_to_nat(26u);
x_67 = lean_unsigned_to_nat(41u);
x_68 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_69 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_64, x_65, x_66, x_67, x_68);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_64);
x_70 = l_panic___at___Lean_Compiler_LCNF_collectLocalDeclsType_go_spec__0(x_69);
return x_70;
}
case 11:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_71 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ElimDead", 27, 27);
x_72 = lean_mk_string_unchecked("Lean.Compiler.LCNF.collectLocalDeclsType.go", 43, 43);
x_73 = lean_unsigned_to_nat(26u);
x_74 = lean_unsigned_to_nat(41u);
x_75 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_76 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_71, x_72, x_73, x_74, x_75);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
x_77 = l_panic___at___Lean_Compiler_LCNF_collectLocalDeclsType_go_spec__0(x_76);
return x_77;
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsType(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_5);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_3);
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
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_3, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
lean_inc(x_3);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_22);
x_30 = lean_array_uset(x_5, x_21, x_29);
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
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_30);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
lean_inc(x_3);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_22);
x_41 = lean_array_uset(x_5, x_21, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_shiftl(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
}
default: 
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = l_Lean_Compiler_LCNF_collectLocalDeclsType_go(x_1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_4, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_collectLocalDeclsArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_4);
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
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_4, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_ctor_get(x_1, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 0);
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_25);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_4);
x_32 = lean_array_uset(x_8, x_24, x_2);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_shiftl(x_31, x_33);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_nat_dec_le(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_32);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 2, x_25);
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_4);
x_42 = lean_array_uset(x_8, x_24, x_2);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_shiftl(x_41, x_43);
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
x_49 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_42);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_free_object(x_2);
lean_dec(x_4);
return x_1;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; size_t x_65; size_t x_66; lean_object* x_67; size_t x_68; size_t x_69; size_t x_70; lean_object* x_71; uint8_t x_72; 
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
lean_dec(x_2);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_array_get_size(x_54);
x_56 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_52);
x_57 = lean_unsigned_to_nat(32u);
x_58 = lean_uint64_of_nat(x_57);
x_59 = lean_uint64_shift_right(x_56, x_58);
x_60 = lean_uint64_xor(x_56, x_59);
x_61 = lean_unsigned_to_nat(16u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_uint64_to_usize(x_64);
x_66 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_usize_of_nat(x_67);
x_69 = lean_usize_sub(x_66, x_68);
x_70 = lean_usize_land(x_65, x_69);
x_71 = lean_array_uget(x_54, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_52, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_73 = x_1;
} else {
 lean_dec_ref(x_1);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
x_75 = lean_nat_add(x_53, x_67);
lean_dec(x_53);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_52);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_71);
x_77 = lean_array_uset(x_54, x_70, x_76);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_shiftl(x_75, x_78);
x_80 = lean_unsigned_to_nat(3u);
x_81 = lean_nat_div(x_79, x_80);
lean_dec(x_79);
x_82 = lean_array_get_size(x_77);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_77);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
else
{
lean_object* x_86; 
if (lean_is_scalar(x_73)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_73;
}
lean_ctor_set(x_86, 0, x_75);
lean_ctor_set(x_86, 1, x_77);
return x_86;
}
}
else
{
lean_dec(x_71);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
return x_1;
}
}
}
case 3:
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
lean_dec(x_2);
x_88 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_87);
lean_dec(x_87);
return x_88;
}
case 4:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; lean_object* x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; lean_object* x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; size_t x_103; size_t x_104; lean_object* x_105; size_t x_106; size_t x_107; size_t x_108; lean_object* x_109; uint8_t x_110; 
x_89 = lean_ctor_get(x_2, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
lean_dec(x_2);
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 1);
lean_inc(x_92);
x_93 = lean_array_get_size(x_92);
x_94 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_89);
x_95 = lean_unsigned_to_nat(32u);
x_96 = lean_uint64_of_nat(x_95);
x_97 = lean_uint64_shift_right(x_94, x_96);
x_98 = lean_uint64_xor(x_94, x_97);
x_99 = lean_unsigned_to_nat(16u);
x_100 = lean_uint64_of_nat(x_99);
x_101 = lean_uint64_shift_right(x_98, x_100);
x_102 = lean_uint64_xor(x_98, x_101);
x_103 = lean_uint64_to_usize(x_102);
x_104 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_usize_of_nat(x_105);
x_107 = lean_usize_sub(x_104, x_106);
x_108 = lean_usize_land(x_103, x_107);
x_109 = lean_array_uget(x_92, x_108);
x_110 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_89, x_109);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_1);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_112 = lean_ctor_get(x_1, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_1, 0);
lean_dec(x_113);
x_114 = lean_box(0);
x_115 = lean_nat_add(x_91, x_105);
lean_dec(x_91);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_89);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_116, 2, x_109);
x_117 = lean_array_uset(x_92, x_108, x_116);
x_118 = lean_unsigned_to_nat(2u);
x_119 = lean_nat_shiftl(x_115, x_118);
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_nat_div(x_119, x_120);
lean_dec(x_119);
x_122 = lean_array_get_size(x_117);
x_123 = lean_nat_dec_le(x_121, x_122);
lean_dec(x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_117);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_115);
x_125 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_90);
lean_dec(x_90);
return x_125;
}
else
{
lean_object* x_126; 
lean_ctor_set(x_1, 1, x_117);
lean_ctor_set(x_1, 0, x_115);
x_126 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_90);
lean_dec(x_90);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_1);
x_127 = lean_box(0);
x_128 = lean_nat_add(x_91, x_105);
lean_dec(x_91);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_89);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_109);
x_130 = lean_array_uset(x_92, x_108, x_129);
x_131 = lean_unsigned_to_nat(2u);
x_132 = lean_nat_shiftl(x_128, x_131);
x_133 = lean_unsigned_to_nat(3u);
x_134 = lean_nat_div(x_132, x_133);
lean_dec(x_132);
x_135 = lean_array_get_size(x_130);
x_136 = lean_nat_dec_le(x_134, x_135);
lean_dec(x_135);
lean_dec(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_130);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_128);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_138, x_90);
lean_dec(x_90);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_130);
x_141 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_140, x_90);
lean_dec(x_90);
return x_141;
}
}
}
else
{
lean_object* x_142; 
lean_dec(x_109);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
x_142 = l_Lean_Compiler_LCNF_collectLocalDeclsArgs(x_1, x_90);
lean_dec(x_90);
return x_142;
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_5, x_1);
x_8 = lean_st_ref_set(x_2, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_9, x_1);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectArgM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_5, x_1);
x_8 = lean_st_ref_set(x_2, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_9, x_1);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectLetValueM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; lean_object* x_30; size_t x_31; size_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = l_Lean_instBEqFVarId;
x_10 = lean_box(0);
x_18 = lean_array_get_size(x_8);
x_19 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_20 = lean_unsigned_to_nat(32u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_unsigned_to_nat(16u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_usize_of_nat(x_30);
x_32 = lean_usize_sub(x_29, x_31);
x_33 = lean_usize_land(x_28, x_32);
x_34 = lean_array_uget(x_8, x_33);
lean_inc(x_34);
lean_inc(x_1);
x_35 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_9, x_1, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_37 = lean_ctor_get(x_5, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 0);
lean_dec(x_38);
x_39 = lean_nat_add(x_7, x_30);
lean_dec(x_7);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_10);
lean_ctor_set(x_40, 2, x_34);
x_41 = lean_array_uset(x_8, x_33, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_shiftl(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_instHashableFVarId;
x_49 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_48, x_41);
lean_ctor_set(x_5, 1, x_49);
lean_ctor_set(x_5, 0, x_39);
x_11 = x_5;
goto block_17;
}
else
{
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_39);
x_11 = x_5;
goto block_17;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_5);
x_50 = lean_nat_add(x_7, x_30);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_10);
lean_ctor_set(x_51, 2, x_34);
x_52 = lean_array_uset(x_8, x_33, x_51);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_shiftl(x_50, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = lean_array_get_size(x_52);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lean_instHashableFVarId;
x_60 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_59, x_52);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_60);
x_11 = x_61;
goto block_17;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_52);
x_11 = x_62;
goto block_17;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = x_5;
goto block_17;
}
block_17:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_set(x_2, x_11, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; lean_object* x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = l_Lean_instBEqFVarId;
x_14 = lean_box(0);
x_22 = lean_array_get_size(x_12);
x_23 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_sub(x_33, x_35);
x_37 = lean_usize_land(x_32, x_36);
x_38 = lean_array_uget(x_12, x_37);
lean_inc(x_38);
lean_inc(x_1);
x_39 = l_Std_DHashMap_Internal_AssocList_contains(lean_box(0), lean_box(0), x_13, x_1, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_41 = lean_ctor_get(x_9, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_9, 0);
lean_dec(x_42);
x_43 = lean_nat_add(x_11, x_34);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_14);
lean_ctor_set(x_44, 2, x_38);
x_45 = lean_array_uset(x_12, x_37, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_shiftl(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_instHashableFVarId;
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_52, x_45);
lean_ctor_set(x_9, 1, x_53);
lean_ctor_set(x_9, 0, x_43);
x_15 = x_9;
goto block_21;
}
else
{
lean_ctor_set(x_9, 1, x_45);
lean_ctor_set(x_9, 0, x_43);
x_15 = x_9;
goto block_21;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_9);
x_54 = lean_nat_add(x_11, x_34);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_14);
lean_ctor_set(x_55, 2, x_38);
x_56 = lean_array_uset(x_12, x_37, x_55);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_nat_shiftl(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = l_Lean_instHashableFVarId;
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_63, x_56);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_64);
x_15 = x_65;
goto block_21;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_56);
x_15 = x_66;
goto block_21;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = x_9;
goto block_21;
}
block_21:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_set(x_2, x_15, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ElimDead_0__Lean_Compiler_LCNF_ElimDead_collectFVarM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_12, x_13, x_10, x_4, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_4);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_Compiler_LCNF_collectLocalDeclsArg(x_9, x_11);
lean_dec(x_11);
x_13 = lean_st_ref_set(x_5, x_12, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
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
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 2);
lean_inc(x_29);
x_13 = x_29;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
x_13 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_14 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint64_t x_124; lean_object* x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; size_t x_133; size_t x_134; lean_object* x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
lean_inc(x_114);
x_115 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_114, x_2, x_3, x_4, x_5, x_6, x_7);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_st_ref_get(x_2, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_113, 0);
lean_inc(x_122);
x_123 = lean_array_get_size(x_121);
x_124 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_122);
x_125 = lean_unsigned_to_nat(32u);
x_126 = lean_uint64_of_nat(x_125);
x_127 = lean_uint64_shift_right(x_124, x_126);
x_128 = lean_uint64_xor(x_124, x_127);
x_129 = lean_unsigned_to_nat(16u);
x_130 = lean_uint64_of_nat(x_129);
x_131 = lean_uint64_shift_right(x_128, x_130);
x_132 = lean_uint64_xor(x_128, x_131);
x_133 = lean_uint64_to_usize(x_132);
x_134 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_usize_of_nat(x_135);
x_137 = lean_usize_sub(x_134, x_136);
x_138 = lean_usize_land(x_133, x_137);
x_139 = lean_array_uget(x_121, x_138);
lean_dec(x_121);
x_140 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_122, x_139);
lean_dec(x_139);
lean_dec(x_122);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
lean_dec(x_114);
lean_dec(x_1);
x_141 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_113, x_4, x_120);
lean_dec(x_113);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 0);
lean_dec(x_143);
lean_ctor_set(x_141, 0, x_116);
return x_141;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_116);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_146 = lean_st_ref_take(x_2, x_120);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_113, 3);
lean_inc(x_149);
x_150 = l_Lean_Compiler_LCNF_collectLocalDeclsLetValue(x_147, x_149);
x_151 = lean_st_ref_set(x_2, x_150, x_148);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; size_t x_154; size_t x_155; uint8_t x_156; 
x_153 = lean_ctor_get(x_151, 0);
lean_dec(x_153);
x_154 = lean_ptr_addr(x_114);
lean_dec(x_114);
x_155 = lean_ptr_addr(x_116);
x_156 = lean_usize_dec_eq(x_154, x_155);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_1);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_1, 1);
lean_dec(x_158);
x_159 = lean_ctor_get(x_1, 0);
lean_dec(x_159);
lean_ctor_set(x_1, 1, x_116);
lean_ctor_set(x_151, 0, x_1);
return x_151;
}
else
{
lean_object* x_160; 
lean_dec(x_1);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_113);
lean_ctor_set(x_160, 1, x_116);
lean_ctor_set(x_151, 0, x_160);
return x_151;
}
}
else
{
lean_dec(x_116);
lean_dec(x_113);
lean_ctor_set(x_151, 0, x_1);
return x_151;
}
}
else
{
lean_object* x_161; size_t x_162; size_t x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_151, 1);
lean_inc(x_161);
lean_dec(x_151);
x_162 = lean_ptr_addr(x_114);
lean_dec(x_114);
x_163 = lean_ptr_addr(x_116);
x_164 = lean_usize_dec_eq(x_162, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_165 = x_1;
} else {
 lean_dec_ref(x_1);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_113);
lean_ctor_set(x_166, 1, x_116);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
return x_167;
}
else
{
lean_object* x_168; 
lean_dec(x_116);
lean_dec(x_113);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_161);
return x_168;
}
}
}
}
case 3:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint64_t x_209; lean_object* x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; lean_object* x_214; uint64_t x_215; uint64_t x_216; uint64_t x_217; size_t x_218; size_t x_219; lean_object* x_220; size_t x_221; size_t x_222; size_t x_223; lean_object* x_224; uint8_t x_225; 
x_169 = lean_ctor_get(x_1, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_1, 1);
lean_inc(x_170);
x_171 = lean_st_ref_take(x_2, x_7);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_206 = lean_ctor_get(x_172, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_172, 1);
lean_inc(x_207);
x_208 = lean_array_get_size(x_207);
x_209 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_169);
x_210 = lean_unsigned_to_nat(32u);
x_211 = lean_uint64_of_nat(x_210);
x_212 = lean_uint64_shift_right(x_209, x_211);
x_213 = lean_uint64_xor(x_209, x_212);
x_214 = lean_unsigned_to_nat(16u);
x_215 = lean_uint64_of_nat(x_214);
x_216 = lean_uint64_shift_right(x_213, x_215);
x_217 = lean_uint64_xor(x_213, x_216);
x_218 = lean_uint64_to_usize(x_217);
x_219 = lean_usize_of_nat(x_208);
lean_dec(x_208);
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_usize_of_nat(x_220);
x_222 = lean_usize_sub(x_219, x_221);
x_223 = lean_usize_land(x_218, x_222);
x_224 = lean_array_uget(x_207, x_223);
x_225 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_169, x_224);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_172);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_227 = lean_ctor_get(x_172, 1);
lean_dec(x_227);
x_228 = lean_ctor_get(x_172, 0);
lean_dec(x_228);
x_229 = lean_box(0);
x_230 = lean_nat_add(x_206, x_220);
lean_dec(x_206);
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_169);
lean_ctor_set(x_231, 1, x_229);
lean_ctor_set(x_231, 2, x_224);
x_232 = lean_array_uset(x_207, x_223, x_231);
x_233 = lean_unsigned_to_nat(2u);
x_234 = lean_nat_shiftl(x_230, x_233);
x_235 = lean_unsigned_to_nat(3u);
x_236 = lean_nat_div(x_234, x_235);
lean_dec(x_234);
x_237 = lean_array_get_size(x_232);
x_238 = lean_nat_dec_le(x_236, x_237);
lean_dec(x_237);
lean_dec(x_236);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_232);
lean_ctor_set(x_172, 1, x_239);
lean_ctor_set(x_172, 0, x_230);
x_174 = x_172;
goto block_205;
}
else
{
lean_ctor_set(x_172, 1, x_232);
lean_ctor_set(x_172, 0, x_230);
x_174 = x_172;
goto block_205;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
lean_dec(x_172);
x_240 = lean_box(0);
x_241 = lean_nat_add(x_206, x_220);
lean_dec(x_206);
x_242 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_242, 0, x_169);
lean_ctor_set(x_242, 1, x_240);
lean_ctor_set(x_242, 2, x_224);
x_243 = lean_array_uset(x_207, x_223, x_242);
x_244 = lean_unsigned_to_nat(2u);
x_245 = lean_nat_shiftl(x_241, x_244);
x_246 = lean_unsigned_to_nat(3u);
x_247 = lean_nat_div(x_245, x_246);
lean_dec(x_245);
x_248 = lean_array_get_size(x_243);
x_249 = lean_nat_dec_le(x_247, x_248);
lean_dec(x_248);
lean_dec(x_247);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_243);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_241);
lean_ctor_set(x_251, 1, x_250);
x_174 = x_251;
goto block_205;
}
else
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_241);
lean_ctor_set(x_252, 1, x_243);
x_174 = x_252;
goto block_205;
}
}
}
else
{
lean_dec(x_224);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_169);
x_174 = x_172;
goto block_205;
}
block_205:
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_st_ref_set(x_2, x_174, x_173);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_177 = lean_ctor_get(x_175, 1);
x_178 = lean_ctor_get(x_175, 0);
lean_dec(x_178);
x_179 = lean_unsigned_to_nat(0u);
x_180 = lean_array_get_size(x_170);
x_181 = lean_nat_dec_lt(x_179, x_180);
if (x_181 == 0)
{
lean_dec(x_180);
lean_dec(x_170);
lean_ctor_set(x_175, 0, x_1);
return x_175;
}
else
{
uint8_t x_182; 
x_182 = lean_nat_dec_le(x_180, x_180);
if (x_182 == 0)
{
lean_dec(x_180);
lean_dec(x_170);
lean_ctor_set(x_175, 0, x_1);
return x_175;
}
else
{
lean_object* x_183; size_t x_184; size_t x_185; lean_object* x_186; uint8_t x_187; 
lean_free_object(x_175);
x_183 = lean_box(0);
x_184 = lean_usize_of_nat(x_179);
x_185 = lean_usize_of_nat(x_180);
lean_dec(x_180);
x_186 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_170, x_184, x_185, x_183, x_2, x_177);
lean_dec(x_170);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 0);
lean_dec(x_188);
lean_ctor_set(x_186, 0, x_1);
return x_186;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_175, 1);
lean_inc(x_191);
lean_dec(x_175);
x_192 = lean_unsigned_to_nat(0u);
x_193 = lean_array_get_size(x_170);
x_194 = lean_nat_dec_lt(x_192, x_193);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_193);
lean_dec(x_170);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_1);
lean_ctor_set(x_195, 1, x_191);
return x_195;
}
else
{
uint8_t x_196; 
x_196 = lean_nat_dec_le(x_193, x_193);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_193);
lean_dec(x_170);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_1);
lean_ctor_set(x_197, 1, x_191);
return x_197;
}
else
{
lean_object* x_198; size_t x_199; size_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_198 = lean_box(0);
x_199 = lean_usize_of_nat(x_192);
x_200 = lean_usize_of_nat(x_193);
lean_dec(x_193);
x_201 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_170, x_199, x_200, x_198, x_2, x_191);
lean_dec(x_170);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_1);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
}
case 4:
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint64_t x_297; lean_object* x_298; uint64_t x_299; uint64_t x_300; uint64_t x_301; lean_object* x_302; uint64_t x_303; uint64_t x_304; uint64_t x_305; size_t x_306; size_t x_307; lean_object* x_308; size_t x_309; size_t x_310; size_t x_311; lean_object* x_312; uint8_t x_313; 
x_253 = lean_ctor_get(x_1, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_253, 3);
lean_inc(x_254);
x_255 = lean_unsigned_to_nat(0u);
lean_inc(x_254);
x_256 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1(x_255, x_254, x_2, x_3, x_4, x_5, x_6, x_7);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_st_ref_take(x_2, x_258);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_293 = lean_ctor_get(x_260, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_260, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_253, 2);
lean_inc(x_295);
x_296 = lean_array_get_size(x_294);
x_297 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_295);
x_298 = lean_unsigned_to_nat(32u);
x_299 = lean_uint64_of_nat(x_298);
x_300 = lean_uint64_shift_right(x_297, x_299);
x_301 = lean_uint64_xor(x_297, x_300);
x_302 = lean_unsigned_to_nat(16u);
x_303 = lean_uint64_of_nat(x_302);
x_304 = lean_uint64_shift_right(x_301, x_303);
x_305 = lean_uint64_xor(x_301, x_304);
x_306 = lean_uint64_to_usize(x_305);
x_307 = lean_usize_of_nat(x_296);
lean_dec(x_296);
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_usize_of_nat(x_308);
x_310 = lean_usize_sub(x_307, x_309);
x_311 = lean_usize_land(x_306, x_310);
x_312 = lean_array_uget(x_294, x_311);
x_313 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_295, x_312);
if (x_313 == 0)
{
uint8_t x_314; 
x_314 = !lean_is_exclusive(x_260);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_315 = lean_ctor_get(x_260, 1);
lean_dec(x_315);
x_316 = lean_ctor_get(x_260, 0);
lean_dec(x_316);
x_317 = lean_box(0);
x_318 = lean_nat_add(x_293, x_308);
lean_dec(x_293);
x_319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_319, 0, x_295);
lean_ctor_set(x_319, 1, x_317);
lean_ctor_set(x_319, 2, x_312);
x_320 = lean_array_uset(x_294, x_311, x_319);
x_321 = lean_unsigned_to_nat(2u);
x_322 = lean_nat_shiftl(x_318, x_321);
x_323 = lean_unsigned_to_nat(3u);
x_324 = lean_nat_div(x_322, x_323);
lean_dec(x_322);
x_325 = lean_array_get_size(x_320);
x_326 = lean_nat_dec_le(x_324, x_325);
lean_dec(x_325);
lean_dec(x_324);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_320);
lean_ctor_set(x_260, 1, x_327);
lean_ctor_set(x_260, 0, x_318);
x_262 = x_260;
goto block_292;
}
else
{
lean_ctor_set(x_260, 1, x_320);
lean_ctor_set(x_260, 0, x_318);
x_262 = x_260;
goto block_292;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec(x_260);
x_328 = lean_box(0);
x_329 = lean_nat_add(x_293, x_308);
lean_dec(x_293);
x_330 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_330, 0, x_295);
lean_ctor_set(x_330, 1, x_328);
lean_ctor_set(x_330, 2, x_312);
x_331 = lean_array_uset(x_294, x_311, x_330);
x_332 = lean_unsigned_to_nat(2u);
x_333 = lean_nat_shiftl(x_329, x_332);
x_334 = lean_unsigned_to_nat(3u);
x_335 = lean_nat_div(x_333, x_334);
lean_dec(x_333);
x_336 = lean_array_get_size(x_331);
x_337 = lean_nat_dec_le(x_335, x_336);
lean_dec(x_336);
lean_dec(x_335);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_331);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_329);
lean_ctor_set(x_339, 1, x_338);
x_262 = x_339;
goto block_292;
}
else
{
lean_object* x_340; 
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_329);
lean_ctor_set(x_340, 1, x_331);
x_262 = x_340;
goto block_292;
}
}
}
else
{
lean_dec(x_312);
lean_dec(x_295);
lean_dec(x_294);
lean_dec(x_293);
x_262 = x_260;
goto block_292;
}
block_292:
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_st_ref_set(x_2, x_262, x_261);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; size_t x_266; size_t x_267; uint8_t x_268; 
x_265 = lean_ctor_get(x_263, 0);
lean_dec(x_265);
x_266 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_267 = lean_ptr_addr(x_257);
x_268 = lean_usize_dec_eq(x_266, x_267);
if (x_268 == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_1);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_1, 0);
lean_dec(x_270);
x_271 = lean_ctor_get(x_253, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_253, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_253, 2);
lean_inc(x_273);
lean_dec(x_253);
x_274 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
lean_ctor_set(x_274, 2, x_273);
lean_ctor_set(x_274, 3, x_257);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set(x_263, 0, x_1);
return x_263;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_1);
x_275 = lean_ctor_get(x_253, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_253, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_253, 2);
lean_inc(x_277);
lean_dec(x_253);
x_278 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
lean_ctor_set(x_278, 2, x_277);
lean_ctor_set(x_278, 3, x_257);
x_279 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_263, 0, x_279);
return x_263;
}
}
else
{
lean_dec(x_257);
lean_dec(x_253);
lean_ctor_set(x_263, 0, x_1);
return x_263;
}
}
else
{
lean_object* x_280; size_t x_281; size_t x_282; uint8_t x_283; 
x_280 = lean_ctor_get(x_263, 1);
lean_inc(x_280);
lean_dec(x_263);
x_281 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_282 = lean_ptr_addr(x_257);
x_283 = lean_usize_dec_eq(x_281, x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_284 = x_1;
} else {
 lean_dec_ref(x_1);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_253, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_253, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_253, 2);
lean_inc(x_287);
lean_dec(x_253);
x_288 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
lean_ctor_set(x_288, 2, x_287);
lean_ctor_set(x_288, 3, x_257);
if (lean_is_scalar(x_284)) {
 x_289 = lean_alloc_ctor(4, 1, 0);
} else {
 x_289 = x_284;
}
lean_ctor_set(x_289, 0, x_288);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_280);
return x_290;
}
else
{
lean_object* x_291; 
lean_dec(x_257);
lean_dec(x_253);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_1);
lean_ctor_set(x_291, 1, x_280);
return x_291;
}
}
}
}
case 5:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint64_t x_355; lean_object* x_356; uint64_t x_357; uint64_t x_358; uint64_t x_359; lean_object* x_360; uint64_t x_361; uint64_t x_362; uint64_t x_363; size_t x_364; size_t x_365; lean_object* x_366; size_t x_367; size_t x_368; size_t x_369; lean_object* x_370; uint8_t x_371; 
x_341 = lean_ctor_get(x_1, 0);
lean_inc(x_341);
x_342 = lean_st_ref_take(x_2, x_7);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_352 = lean_ctor_get(x_343, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_343, 1);
lean_inc(x_353);
x_354 = lean_array_get_size(x_353);
x_355 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_341);
x_356 = lean_unsigned_to_nat(32u);
x_357 = lean_uint64_of_nat(x_356);
x_358 = lean_uint64_shift_right(x_355, x_357);
x_359 = lean_uint64_xor(x_355, x_358);
x_360 = lean_unsigned_to_nat(16u);
x_361 = lean_uint64_of_nat(x_360);
x_362 = lean_uint64_shift_right(x_359, x_361);
x_363 = lean_uint64_xor(x_359, x_362);
x_364 = lean_uint64_to_usize(x_363);
x_365 = lean_usize_of_nat(x_354);
lean_dec(x_354);
x_366 = lean_unsigned_to_nat(1u);
x_367 = lean_usize_of_nat(x_366);
x_368 = lean_usize_sub(x_365, x_367);
x_369 = lean_usize_land(x_364, x_368);
x_370 = lean_array_uget(x_353, x_369);
x_371 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_341, x_370);
if (x_371 == 0)
{
uint8_t x_372; 
x_372 = !lean_is_exclusive(x_343);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_373 = lean_ctor_get(x_343, 1);
lean_dec(x_373);
x_374 = lean_ctor_get(x_343, 0);
lean_dec(x_374);
x_375 = lean_box(0);
x_376 = lean_nat_add(x_352, x_366);
lean_dec(x_352);
x_377 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_377, 0, x_341);
lean_ctor_set(x_377, 1, x_375);
lean_ctor_set(x_377, 2, x_370);
x_378 = lean_array_uset(x_353, x_369, x_377);
x_379 = lean_unsigned_to_nat(2u);
x_380 = lean_nat_shiftl(x_376, x_379);
x_381 = lean_unsigned_to_nat(3u);
x_382 = lean_nat_div(x_380, x_381);
lean_dec(x_380);
x_383 = lean_array_get_size(x_378);
x_384 = lean_nat_dec_le(x_382, x_383);
lean_dec(x_383);
lean_dec(x_382);
if (x_384 == 0)
{
lean_object* x_385; 
x_385 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_378);
lean_ctor_set(x_343, 1, x_385);
lean_ctor_set(x_343, 0, x_376);
x_345 = x_343;
goto block_351;
}
else
{
lean_ctor_set(x_343, 1, x_378);
lean_ctor_set(x_343, 0, x_376);
x_345 = x_343;
goto block_351;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
lean_dec(x_343);
x_386 = lean_box(0);
x_387 = lean_nat_add(x_352, x_366);
lean_dec(x_352);
x_388 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_388, 0, x_341);
lean_ctor_set(x_388, 1, x_386);
lean_ctor_set(x_388, 2, x_370);
x_389 = lean_array_uset(x_353, x_369, x_388);
x_390 = lean_unsigned_to_nat(2u);
x_391 = lean_nat_shiftl(x_387, x_390);
x_392 = lean_unsigned_to_nat(3u);
x_393 = lean_nat_div(x_391, x_392);
lean_dec(x_391);
x_394 = lean_array_get_size(x_389);
x_395 = lean_nat_dec_le(x_393, x_394);
lean_dec(x_394);
lean_dec(x_393);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
x_396 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_389);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_387);
lean_ctor_set(x_397, 1, x_396);
x_345 = x_397;
goto block_351;
}
else
{
lean_object* x_398; 
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_387);
lean_ctor_set(x_398, 1, x_389);
x_345 = x_398;
goto block_351;
}
}
}
else
{
lean_dec(x_370);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_341);
x_345 = x_343;
goto block_351;
}
block_351:
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_st_ref_set(x_2, x_345, x_344);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_346, 0);
lean_dec(x_348);
lean_ctor_set(x_346, 0, x_1);
return x_346;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_1);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
case 6:
{
lean_object* x_399; 
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_1);
lean_ctor_set(x_399, 1, x_7);
return x_399;
}
default: 
{
lean_object* x_400; lean_object* x_401; 
x_400 = lean_ctor_get(x_1, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_1, 1);
lean_inc(x_401);
x_32 = x_400;
x_33 = x_401;
x_34 = x_2;
x_35 = x_3;
x_36 = x_4;
x_37 = x_5;
x_38 = x_6;
x_39 = x_7;
goto block_112;
}
}
block_19:
{
if (x_12 == 0)
{
if (x_11 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
block_31:
{
if (x_24 == 0)
{
if (x_23 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
if (x_23 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
block_112:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; size_t x_58; size_t x_59; lean_object* x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; uint8_t x_65; 
x_40 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_33, x_34, x_35, x_36, x_37, x_38, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_34, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_46);
x_49 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_47);
x_50 = lean_unsigned_to_nat(32u);
x_51 = lean_uint64_of_nat(x_50);
x_52 = lean_uint64_shift_right(x_49, x_51);
x_53 = lean_uint64_xor(x_49, x_52);
x_54 = lean_unsigned_to_nat(16u);
x_55 = lean_uint64_of_nat(x_54);
x_56 = lean_uint64_shift_right(x_53, x_55);
x_57 = lean_uint64_xor(x_53, x_56);
x_58 = lean_uint64_to_usize(x_57);
x_59 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_usize_of_nat(x_60);
x_62 = lean_usize_sub(x_59, x_61);
x_63 = lean_usize_land(x_58, x_62);
x_64 = lean_array_uget(x_46, x_63);
lean_dec(x_46);
x_65 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_47, x_64);
lean_dec(x_64);
lean_dec(x_47);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_1);
x_66 = lean_box(1);
x_67 = lean_unbox(x_66);
x_68 = l_Lean_Compiler_LCNF_eraseFunDecl(x_32, x_67, x_35, x_36, x_37, x_38, x_45);
lean_dec(x_32);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_41);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_41);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; 
x_73 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_32, x_34, x_35, x_36, x_37, x_38, x_45);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; uint8_t x_80; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
x_78 = lean_ptr_addr(x_77);
lean_dec(x_77);
x_79 = lean_ptr_addr(x_41);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_dec(x_76);
x_8 = x_74;
x_9 = x_75;
x_10 = x_41;
x_11 = x_65;
x_12 = x_80;
goto block_19;
}
else
{
size_t x_81; size_t x_82; uint8_t x_83; 
x_81 = lean_ptr_addr(x_76);
lean_dec(x_76);
x_82 = lean_ptr_addr(x_74);
x_83 = lean_usize_dec_eq(x_81, x_82);
x_8 = x_74;
x_9 = x_75;
x_10 = x_41;
x_11 = x_65;
x_12 = x_83;
goto block_19;
}
}
case 2:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; uint8_t x_90; 
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
lean_dec(x_73);
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = lean_ptr_addr(x_87);
lean_dec(x_87);
x_89 = lean_ptr_addr(x_41);
x_90 = lean_usize_dec_eq(x_88, x_89);
if (x_90 == 0)
{
lean_dec(x_86);
x_20 = x_84;
x_21 = x_85;
x_22 = x_41;
x_23 = x_65;
x_24 = x_90;
goto block_31;
}
else
{
size_t x_91; size_t x_92; uint8_t x_93; 
x_91 = lean_ptr_addr(x_86);
lean_dec(x_86);
x_92 = lean_ptr_addr(x_84);
x_93 = lean_usize_dec_eq(x_91, x_92);
x_20 = x_84;
x_21 = x_85;
x_22 = x_41;
x_23 = x_65;
x_24 = x_93;
goto block_31;
}
}
default: 
{
uint8_t x_94; 
lean_dec(x_41);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_73);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_73, 0);
lean_dec(x_95);
x_96 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_97 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_98 = lean_unsigned_to_nat(305u);
x_99 = lean_unsigned_to_nat(9u);
x_100 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_101 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_96, x_97, x_98, x_99, x_100);
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_96);
x_102 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_101);
lean_ctor_set(x_73, 0, x_102);
return x_73;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_73, 1);
lean_inc(x_103);
lean_dec(x_73);
x_104 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_105 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_106 = lean_unsigned_to_nat(305u);
x_107 = lean_unsigned_to_nat(9u);
x_108 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_109 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_104, x_105, x_106, x_107, x_108);
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_104);
x_110 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_103);
return x_111;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_visitFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ElimDead_visitFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ElimDead_elimDead_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ElimDead_elimDead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_7, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_st_mk_ref(x_16, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_LCNF_ElimDead_elimDead(x_1, x_18, x_2, x_3, x_4, x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_18, x_22);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_elimDead___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_elimDead(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_apply_6(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_6(x_1, x_20, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_elimDead(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_elimDead___boxed), 6, 0);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_elimDead_spec__0(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_18 = lean_ctor_get(x_1, 5);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_11);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*6, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*6 + 1, x_17);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_28 = lean_ctor_get(x_1, 5);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_20);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*6, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
