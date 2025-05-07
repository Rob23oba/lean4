// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PropagatorAttr
// Imports: Init.Grind Lean.Meta.Tactic.Grind.Proof
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedBuiltinPropagators;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__1(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__1____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at___Lean_ensureNoOverload___at___Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_List_filterMapTR_go___at___Lean_preprocessSyntaxAndResolve___at___Lean_realizeGlobalConst_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_builtinPropagatorsRef;
lean_object* l_List_mapTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_ensureNonAmbiguous___at___Lean_realizeGlobalConstNoOverload_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_throwErrorAt___at___Lean_Meta_mkProjections_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_52_(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__1___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__1____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__0(uint8_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedBuiltinPropagators() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_52_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
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
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_st_mk_ref(x_12, x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_initializing(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_mk_string_unchecked("invalid builtin `grind` propagator declaration, it can only be registered during initialization", 95, 95);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_mk_string_unchecked("invalid builtin `grind` propagator declaration, it can only be registered during initialization", 95, 95);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
if (x_2 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_Lean_Meta_Grind_builtinPropagatorsRef;
x_18 = lean_st_ref_get(x_17, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Name_hash___override(x_1);
x_27 = lean_unsigned_to_nat(32u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_sub(x_36, x_38);
x_40 = lean_usize_land(x_35, x_39);
x_41 = lean_array_uget(x_24, x_40);
lean_dec(x_24);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_57; 
lean_free_object(x_18);
x_43 = lean_st_ref_take(x_17, x_22);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; size_t x_63; lean_object* x_64; uint8_t x_65; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
x_60 = lean_array_get_size(x_59);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = lean_usize_sub(x_61, x_38);
x_63 = lean_usize_land(x_35, x_62);
x_64 = lean_array_uget(x_59, x_63);
x_65 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_66 = lean_nat_add(x_58, x_37);
lean_dec(x_58);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_3);
lean_ctor_set(x_67, 2, x_64);
x_68 = lean_array_uset(x_59, x_63, x_67);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_shiftl(x_66, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = lean_array_get_size(x_68);
x_74 = lean_nat_dec_le(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_68);
lean_ctor_set(x_47, 1, x_75);
lean_ctor_set(x_47, 0, x_66);
x_49 = x_47;
goto block_56;
}
else
{
lean_ctor_set(x_47, 1, x_68);
lean_ctor_set(x_47, 0, x_66);
x_49 = x_47;
goto block_56;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_box(0);
x_77 = lean_array_uset(x_59, x_63, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_64);
x_79 = lean_array_uset(x_77, x_63, x_78);
lean_ctor_set(x_47, 1, x_79);
x_49 = x_47;
goto block_56;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_47, 0);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_47);
x_82 = lean_array_get_size(x_81);
x_83 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_84 = lean_usize_sub(x_83, x_38);
x_85 = lean_usize_land(x_35, x_84);
x_86 = lean_array_uget(x_81, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_88 = lean_nat_add(x_80, x_37);
lean_dec(x_80);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_3);
lean_ctor_set(x_89, 2, x_86);
x_90 = lean_array_uset(x_81, x_85, x_89);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_shiftl(x_88, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_49 = x_98;
goto block_56;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_90);
x_49 = x_99;
goto block_56;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_81, x_85, x_100);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_86);
x_103 = lean_array_uset(x_101, x_85, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_80);
lean_ctor_set(x_104, 1, x_103);
x_49 = x_104;
goto block_56;
}
}
block_56:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_st_ref_set(x_17, x_50, x_45);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_3);
x_105 = lean_box(x_2);
x_106 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__0___boxed), 2, 1);
lean_closure_set(x_106, 0, x_105);
x_107 = lean_mk_string_unchecked("invalid builtin `grind` downward propagator `", 45, 45);
x_108 = l_Lean_Name_toString(x_1, x_42, x_106);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_mk_string_unchecked("`, it has already been declared", 31, 31);
x_111 = lean_string_append(x_109, x_110);
lean_dec(x_110);
x_112 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_112);
return x_18;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint64_t x_116; lean_object* x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; lean_object* x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; size_t x_125; size_t x_126; lean_object* x_127; size_t x_128; size_t x_129; size_t x_130; lean_object* x_131; uint8_t x_132; 
x_113 = lean_ctor_get(x_18, 1);
lean_inc(x_113);
lean_dec(x_18);
x_114 = lean_ctor_get(x_20, 1);
lean_inc(x_114);
lean_dec(x_20);
x_115 = lean_array_get_size(x_114);
x_116 = l_Lean_Name_hash___override(x_1);
x_117 = lean_unsigned_to_nat(32u);
x_118 = lean_uint64_of_nat(x_117);
x_119 = lean_uint64_shift_right(x_116, x_118);
x_120 = lean_uint64_xor(x_116, x_119);
x_121 = lean_unsigned_to_nat(16u);
x_122 = lean_uint64_of_nat(x_121);
x_123 = lean_uint64_shift_right(x_120, x_122);
x_124 = lean_uint64_xor(x_120, x_123);
x_125 = lean_uint64_to_usize(x_124);
x_126 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_usize_of_nat(x_127);
x_129 = lean_usize_sub(x_126, x_128);
x_130 = lean_usize_land(x_125, x_129);
x_131 = lean_array_uget(x_114, x_130);
lean_dec(x_114);
x_132 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; size_t x_153; lean_object* x_154; uint8_t x_155; 
x_133 = lean_st_ref_take(x_17, x_113);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
 x_138 = lean_box(0);
}
x_147 = lean_ctor_get(x_137, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_137, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_149 = x_137;
} else {
 lean_dec_ref(x_137);
 x_149 = lean_box(0);
}
x_150 = lean_array_get_size(x_148);
x_151 = lean_usize_of_nat(x_150);
lean_dec(x_150);
x_152 = lean_usize_sub(x_151, x_128);
x_153 = lean_usize_land(x_125, x_152);
x_154 = lean_array_uget(x_148, x_153);
x_155 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_nat_add(x_147, x_127);
lean_dec(x_147);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_1);
lean_ctor_set(x_157, 1, x_3);
lean_ctor_set(x_157, 2, x_154);
x_158 = lean_array_uset(x_148, x_153, x_157);
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_nat_shiftl(x_156, x_159);
x_161 = lean_unsigned_to_nat(3u);
x_162 = lean_nat_div(x_160, x_161);
lean_dec(x_160);
x_163 = lean_array_get_size(x_158);
x_164 = lean_nat_dec_le(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_158);
if (lean_is_scalar(x_149)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_149;
}
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_165);
x_139 = x_166;
goto block_146;
}
else
{
lean_object* x_167; 
if (lean_is_scalar(x_149)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_149;
}
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_158);
x_139 = x_167;
goto block_146;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_box(0);
x_169 = lean_array_uset(x_148, x_153, x_168);
x_170 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_154);
x_171 = lean_array_uset(x_169, x_153, x_170);
if (lean_is_scalar(x_149)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_149;
}
lean_ctor_set(x_172, 0, x_147);
lean_ctor_set(x_172, 1, x_171);
x_139 = x_172;
goto block_146;
}
block_146:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_st_ref_set(x_17, x_140, x_135);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_3);
x_173 = lean_box(x_2);
x_174 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__0___boxed), 2, 1);
lean_closure_set(x_174, 0, x_173);
x_175 = lean_mk_string_unchecked("invalid builtin `grind` downward propagator `", 45, 45);
x_176 = l_Lean_Name_toString(x_1, x_132, x_174);
x_177 = lean_string_append(x_175, x_176);
lean_dec(x_176);
x_178 = lean_mk_string_unchecked("`, it has already been declared", 31, 31);
x_179 = lean_string_append(x_177, x_178);
lean_dec(x_178);
x_180 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_113);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_5, 1);
lean_inc(x_182);
lean_dec(x_5);
x_183 = l_Lean_Meta_Grind_builtinPropagatorsRef;
x_184 = lean_st_ref_get(x_183, x_182);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec(x_185);
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint64_t x_192; lean_object* x_193; uint64_t x_194; uint64_t x_195; uint64_t x_196; lean_object* x_197; uint64_t x_198; uint64_t x_199; uint64_t x_200; size_t x_201; size_t x_202; lean_object* x_203; size_t x_204; size_t x_205; size_t x_206; lean_object* x_207; uint8_t x_208; 
x_188 = lean_ctor_get(x_184, 1);
x_189 = lean_ctor_get(x_184, 0);
lean_dec(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_dec(x_186);
x_191 = lean_array_get_size(x_190);
x_192 = l_Lean_Name_hash___override(x_1);
x_193 = lean_unsigned_to_nat(32u);
x_194 = lean_uint64_of_nat(x_193);
x_195 = lean_uint64_shift_right(x_192, x_194);
x_196 = lean_uint64_xor(x_192, x_195);
x_197 = lean_unsigned_to_nat(16u);
x_198 = lean_uint64_of_nat(x_197);
x_199 = lean_uint64_shift_right(x_196, x_198);
x_200 = lean_uint64_xor(x_196, x_199);
x_201 = lean_uint64_to_usize(x_200);
x_202 = lean_usize_of_nat(x_191);
lean_dec(x_191);
x_203 = lean_unsigned_to_nat(1u);
x_204 = lean_usize_of_nat(x_203);
x_205 = lean_usize_sub(x_202, x_204);
x_206 = lean_usize_land(x_201, x_205);
x_207 = lean_array_uget(x_190, x_206);
lean_dec(x_190);
x_208 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_223; 
lean_free_object(x_184);
x_209 = lean_st_ref_take(x_183, x_188);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_214 = x_210;
} else {
 lean_dec_ref(x_210);
 x_214 = lean_box(0);
}
x_223 = !lean_is_exclusive(x_212);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; size_t x_227; size_t x_228; size_t x_229; lean_object* x_230; uint8_t x_231; 
x_224 = lean_ctor_get(x_212, 0);
x_225 = lean_ctor_get(x_212, 1);
x_226 = lean_array_get_size(x_225);
x_227 = lean_usize_of_nat(x_226);
lean_dec(x_226);
x_228 = lean_usize_sub(x_227, x_204);
x_229 = lean_usize_land(x_201, x_228);
x_230 = lean_array_uget(x_225, x_229);
x_231 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_232 = lean_nat_add(x_224, x_203);
lean_dec(x_224);
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_1);
lean_ctor_set(x_233, 1, x_3);
lean_ctor_set(x_233, 2, x_230);
x_234 = lean_array_uset(x_225, x_229, x_233);
x_235 = lean_unsigned_to_nat(2u);
x_236 = lean_nat_shiftl(x_232, x_235);
x_237 = lean_unsigned_to_nat(3u);
x_238 = lean_nat_div(x_236, x_237);
lean_dec(x_236);
x_239 = lean_array_get_size(x_234);
x_240 = lean_nat_dec_le(x_238, x_239);
lean_dec(x_239);
lean_dec(x_238);
if (x_240 == 0)
{
lean_object* x_241; 
x_241 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_234);
lean_ctor_set(x_212, 1, x_241);
lean_ctor_set(x_212, 0, x_232);
x_215 = x_212;
goto block_222;
}
else
{
lean_ctor_set(x_212, 1, x_234);
lean_ctor_set(x_212, 0, x_232);
x_215 = x_212;
goto block_222;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_242 = lean_box(0);
x_243 = lean_array_uset(x_225, x_229, x_242);
x_244 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_230);
x_245 = lean_array_uset(x_243, x_229, x_244);
lean_ctor_set(x_212, 1, x_245);
x_215 = x_212;
goto block_222;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; size_t x_249; size_t x_250; size_t x_251; lean_object* x_252; uint8_t x_253; 
x_246 = lean_ctor_get(x_212, 0);
x_247 = lean_ctor_get(x_212, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_212);
x_248 = lean_array_get_size(x_247);
x_249 = lean_usize_of_nat(x_248);
lean_dec(x_248);
x_250 = lean_usize_sub(x_249, x_204);
x_251 = lean_usize_land(x_201, x_250);
x_252 = lean_array_uget(x_247, x_251);
x_253 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_254 = lean_nat_add(x_246, x_203);
lean_dec(x_246);
x_255 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_255, 0, x_1);
lean_ctor_set(x_255, 1, x_3);
lean_ctor_set(x_255, 2, x_252);
x_256 = lean_array_uset(x_247, x_251, x_255);
x_257 = lean_unsigned_to_nat(2u);
x_258 = lean_nat_shiftl(x_254, x_257);
x_259 = lean_unsigned_to_nat(3u);
x_260 = lean_nat_div(x_258, x_259);
lean_dec(x_258);
x_261 = lean_array_get_size(x_256);
x_262 = lean_nat_dec_le(x_260, x_261);
lean_dec(x_261);
lean_dec(x_260);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_256);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_254);
lean_ctor_set(x_264, 1, x_263);
x_215 = x_264;
goto block_222;
}
else
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_254);
lean_ctor_set(x_265, 1, x_256);
x_215 = x_265;
goto block_222;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_box(0);
x_267 = lean_array_uset(x_247, x_251, x_266);
x_268 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_252);
x_269 = lean_array_uset(x_267, x_251, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_246);
lean_ctor_set(x_270, 1, x_269);
x_215 = x_270;
goto block_222;
}
}
block_222:
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_213);
x_217 = lean_st_ref_set(x_183, x_216, x_211);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
return x_217;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_217);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_3);
x_271 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__1___boxed), 1, 0);
x_272 = lean_mk_string_unchecked("invalid builtin `grind` upward propagator `", 43, 43);
x_273 = l_Lean_Name_toString(x_1, x_208, x_271);
x_274 = lean_string_append(x_272, x_273);
lean_dec(x_273);
x_275 = lean_mk_string_unchecked("`, it has already been declared", 31, 31);
x_276 = lean_string_append(x_274, x_275);
lean_dec(x_275);
x_277 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set_tag(x_184, 1);
lean_ctor_set(x_184, 0, x_277);
return x_184;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; uint64_t x_281; lean_object* x_282; uint64_t x_283; uint64_t x_284; uint64_t x_285; lean_object* x_286; uint64_t x_287; uint64_t x_288; uint64_t x_289; size_t x_290; size_t x_291; lean_object* x_292; size_t x_293; size_t x_294; size_t x_295; lean_object* x_296; uint8_t x_297; 
x_278 = lean_ctor_get(x_184, 1);
lean_inc(x_278);
lean_dec(x_184);
x_279 = lean_ctor_get(x_186, 1);
lean_inc(x_279);
lean_dec(x_186);
x_280 = lean_array_get_size(x_279);
x_281 = l_Lean_Name_hash___override(x_1);
x_282 = lean_unsigned_to_nat(32u);
x_283 = lean_uint64_of_nat(x_282);
x_284 = lean_uint64_shift_right(x_281, x_283);
x_285 = lean_uint64_xor(x_281, x_284);
x_286 = lean_unsigned_to_nat(16u);
x_287 = lean_uint64_of_nat(x_286);
x_288 = lean_uint64_shift_right(x_285, x_287);
x_289 = lean_uint64_xor(x_285, x_288);
x_290 = lean_uint64_to_usize(x_289);
x_291 = lean_usize_of_nat(x_280);
lean_dec(x_280);
x_292 = lean_unsigned_to_nat(1u);
x_293 = lean_usize_of_nat(x_292);
x_294 = lean_usize_sub(x_291, x_293);
x_295 = lean_usize_land(x_290, x_294);
x_296 = lean_array_uget(x_279, x_295);
lean_dec(x_279);
x_297 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_296);
lean_dec(x_296);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; size_t x_316; size_t x_317; size_t x_318; lean_object* x_319; uint8_t x_320; 
x_298 = lean_st_ref_take(x_183, x_278);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_303 = x_299;
} else {
 lean_dec_ref(x_299);
 x_303 = lean_box(0);
}
x_312 = lean_ctor_get(x_301, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_301, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_314 = x_301;
} else {
 lean_dec_ref(x_301);
 x_314 = lean_box(0);
}
x_315 = lean_array_get_size(x_313);
x_316 = lean_usize_of_nat(x_315);
lean_dec(x_315);
x_317 = lean_usize_sub(x_316, x_293);
x_318 = lean_usize_land(x_290, x_317);
x_319 = lean_array_uget(x_313, x_318);
x_320 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_321 = lean_nat_add(x_312, x_292);
lean_dec(x_312);
x_322 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_322, 0, x_1);
lean_ctor_set(x_322, 1, x_3);
lean_ctor_set(x_322, 2, x_319);
x_323 = lean_array_uset(x_313, x_318, x_322);
x_324 = lean_unsigned_to_nat(2u);
x_325 = lean_nat_shiftl(x_321, x_324);
x_326 = lean_unsigned_to_nat(3u);
x_327 = lean_nat_div(x_325, x_326);
lean_dec(x_325);
x_328 = lean_array_get_size(x_323);
x_329 = lean_nat_dec_le(x_327, x_328);
lean_dec(x_328);
lean_dec(x_327);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
x_330 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_323);
if (lean_is_scalar(x_314)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_314;
}
lean_ctor_set(x_331, 0, x_321);
lean_ctor_set(x_331, 1, x_330);
x_304 = x_331;
goto block_311;
}
else
{
lean_object* x_332; 
if (lean_is_scalar(x_314)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_314;
}
lean_ctor_set(x_332, 0, x_321);
lean_ctor_set(x_332, 1, x_323);
x_304 = x_332;
goto block_311;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_333 = lean_box(0);
x_334 = lean_array_uset(x_313, x_318, x_333);
x_335 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_319);
x_336 = lean_array_uset(x_334, x_318, x_335);
if (lean_is_scalar(x_314)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_314;
}
lean_ctor_set(x_337, 0, x_312);
lean_ctor_set(x_337, 1, x_336);
x_304 = x_337;
goto block_311;
}
block_311:
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
if (lean_is_scalar(x_303)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_303;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_302);
x_306 = lean_st_ref_set(x_183, x_305, x_300);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_309 = x_306;
} else {
 lean_dec_ref(x_306);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_3);
x_338 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__1___boxed), 1, 0);
x_339 = lean_mk_string_unchecked("invalid builtin `grind` upward propagator `", 43, 43);
x_340 = l_Lean_Name_toString(x_1, x_297, x_338);
x_341 = lean_string_append(x_339, x_340);
lean_dec(x_340);
x_342 = lean_mk_string_unchecked("`, it has already been declared", 31, 31);
x_343 = lean_string_append(x_341, x_342);
lean_dec(x_342);
x_344 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_344, 0, x_343);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_278);
return x_345;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(x_1, x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_registerBuiltinPropagatorCore(x_1, x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 6);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 7);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_ResolveName_resolveGlobalName(x_8, x_9, x_10, x_1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 7);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_14, x_15, x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__1(x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(0);
x_9 = l_List_filterTR_loop___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__0(x_2, x_8);
x_10 = l_List_isEmpty___redArg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___lam__0(x_9, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1(x_1, x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = l_List_filterMapTR_go___at___Lean_preprocessSyntaxAndResolve___at___Lean_realizeGlobalConst_spec__0_spec__0(x_9, x_11);
x_13 = l_List_isEmpty___redArg(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_5, 5);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_1);
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 6);
x_23 = lean_ctor_get(x_5, 7);
x_24 = lean_ctor_get(x_5, 8);
x_25 = lean_ctor_get(x_5, 9);
x_26 = lean_ctor_get(x_5, 10);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_28 = lean_ctor_get(x_5, 11);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_30 = lean_ctor_get(x_5, 12);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_31 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_16);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set(x_31, 12, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*13, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*13 + 1, x_29);
x_32 = lean_apply_6(x_2, x_8, x_3, x_4, x_31, x_6, x_7);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_33 = lean_mk_string_unchecked("expected identifier", 19, 19);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l_Lean_throwErrorAt___at___Lean_Meta_mkProjections_spec__5___redArg(x_1, x_35, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___lam__0___boxed), 6, 0);
x_8 = l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__3(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_11 = l_instMonadEIO(lean_box(0));
x_12 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_26);
lean_inc(x_23);
lean_inc(x_20);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_20);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_37, 0, x_23);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_26);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_7);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_box(0);
x_44 = l_instInhabitedOfMonad___redArg(x_42, x_43);
x_45 = lean_panic_fn(x_44, x_1);
x_46 = lean_apply_5(x_45, x_2, x_3, x_4, x_5, x_6);
return x_46;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
x_9 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
x_10 = lean_unsigned_to_nat(367u);
x_11 = lean_unsigned_to_nat(11u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__5_spec__5(x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
x_20 = lean_mk_string_unchecked("ambiguous identifier '", 22, 22);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
lean_inc(x_1);
x_24 = l_Lean_Syntax_formatStx(x_1, x_21, x_23);
x_25 = lean_unsigned_to_nat(120u);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_format_pretty(x_24, x_25, x_26, x_26);
x_28 = lean_string_append(x_20, x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("', possible interpretations: ", 29, 29);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = l_List_mapTR_loop___at___Lean_ensureNonAmbiguous___at___Lean_realizeGlobalConstNoOverload_spec__0_spec__1(x_2, x_31);
x_33 = l_List_toString___at___Lean_ensureNoOverload___at___Lean_realizeGlobalConstNoOverloadCore_spec__0_spec__1(x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_30, x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = l_Lean_throwErrorAt___at___Lean_Meta_mkProjections_spec__5___redArg(x_1, x_36, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ensureNonAmbiguous___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__5(x_1, x_8, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Tactic", 6, 6);
x_12 = lean_mk_string_unchecked("simpPost", 8, 8);
lean_inc(x_9);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
x_14 = lean_name_eq(x_8, x_13);
lean_dec(x_13);
lean_dec(x_8);
x_15 = lean_box(1);
if (x_14 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_mk_string_unchecked("Meta", 4, 4);
x_115 = lean_mk_string_unchecked("Grind", 5, 5);
x_116 = lean_mk_string_unchecked("registerBuiltinDownwardPropagator", 33, 33);
x_117 = l_Lean_Name_mkStr4(x_9, x_114, x_115, x_116);
x_16 = x_117;
goto block_113;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_mk_string_unchecked("Meta", 4, 4);
x_119 = lean_mk_string_unchecked("Grind", 5, 5);
x_120 = lean_mk_string_unchecked("registerBuiltinUpwardPropagator", 31, 31);
x_121 = l_Lean_Name_mkStr4(x_9, x_118, x_119, x_120);
x_16 = x_121;
goto block_113;
}
block_113:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint64_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; 
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_box(0);
x_19 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_20 = lean_unsigned_to_nat(5u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_nat_pow(x_17, x_22);
lean_dec(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_19);
lean_inc(x_19);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_19);
lean_inc(x_19);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_19);
lean_inc(x_19);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_19);
lean_inc(x_19);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_19);
lean_inc(x_19);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_19);
lean_inc(x_29);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_31);
lean_ctor_set(x_35, 6, x_32);
lean_ctor_set(x_35, 7, x_33);
lean_ctor_set(x_35, 8, x_34);
lean_inc(x_19);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_19);
lean_inc(x_19);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_19);
lean_inc(x_19);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_19);
lean_inc(x_19);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_19);
lean_inc(x_39);
lean_inc(x_36);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_39);
lean_inc(x_26);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_26);
lean_inc(x_26);
x_42 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_26);
lean_ctor_set(x_42, 2, x_28);
lean_ctor_set(x_42, 3, x_28);
lean_ctor_set_usize(x_42, 4, x_21);
lean_inc(x_19);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_19);
lean_inc_n(x_29, 2);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_29);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_18);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_st_mk_ref(x_45, x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(1);
x_50 = lean_box(0);
x_51 = lean_box(2);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_19);
x_53 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_53, 0, x_27);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_28);
lean_ctor_set(x_53, 3, x_28);
lean_ctor_set_usize(x_53, 4, x_21);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 0, 18);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 0, x_56);
x_57 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 1, x_57);
x_58 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 2, x_58);
x_59 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 3, x_59);
x_60 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 4, x_60);
x_61 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 5, x_61);
x_62 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 6, x_62);
x_63 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 7, x_63);
x_64 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 8, x_64);
x_65 = lean_unbox(x_49);
lean_ctor_set_uint8(x_55, 9, x_65);
x_66 = lean_unbox(x_50);
lean_ctor_set_uint8(x_55, 10, x_66);
x_67 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 11, x_67);
x_68 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 12, x_68);
x_69 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 13, x_69);
x_70 = lean_unbox(x_51);
lean_ctor_set_uint8(x_55, 14, x_70);
x_71 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 15, x_71);
x_72 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 16, x_72);
x_73 = lean_unbox(x_15);
lean_ctor_set_uint8(x_55, 17, x_73);
x_74 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_55);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_52);
lean_ctor_set(x_75, 1, x_53);
lean_ctor_set(x_75, 2, x_18);
x_76 = lean_mk_empty_array_with_capacity(x_28);
x_77 = lean_box(0);
x_78 = lean_box(0);
x_79 = l_Lean_Syntax_getArg(x_2, x_17);
x_80 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_80, 0, x_55);
lean_ctor_set(x_80, 1, x_18);
lean_ctor_set(x_80, 2, x_75);
lean_ctor_set(x_80, 3, x_76);
lean_ctor_set(x_80, 4, x_77);
lean_ctor_set(x_80, 5, x_28);
lean_ctor_set(x_80, 6, x_78);
lean_ctor_set_uint64(x_80, sizeof(void*)*7, x_74);
x_81 = lean_unbox(x_54);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 8, x_81);
x_82 = lean_unbox(x_54);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 9, x_82);
x_83 = lean_unbox(x_54);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 10, x_83);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_47);
x_84 = l_Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0(x_79, x_80, x_47, x_3, x_4, x_48);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_85);
x_88 = lean_mk_empty_array_with_capacity(x_17);
x_89 = lean_mk_string_unchecked("declare", 7, 7);
x_90 = l_Lean_Name_mkStr1(x_89);
lean_inc(x_1);
x_91 = l_Lean_Name_append(x_1, x_90);
x_92 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_91, x_3, x_4, x_86);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_box(0);
x_96 = l_Lean_Expr_const___override(x_1, x_95);
x_97 = lean_array_push(x_88, x_87);
x_98 = l_Lean_Expr_const___override(x_16, x_95);
x_99 = lean_array_push(x_97, x_96);
x_100 = l_Lean_mkAppN(x_98, x_99);
lean_dec(x_99);
x_101 = l_Lean_declareBuiltin(x_93, x_100, x_3, x_4, x_94);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_st_ref_get(x_47, x_103);
lean_dec(x_47);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 0);
lean_dec(x_106);
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
else
{
lean_dec(x_47);
return x_101;
}
}
else
{
uint8_t x_109; 
lean_dec(x_47);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_84);
if (x_109 == 0)
{
return x_84;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_84, 0);
x_111 = lean_ctor_get(x_84, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_84);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalName___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_filterFieldList___at_____private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_preprocessSyntaxAndResolve___at___Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConst___at___Lean_resolveGlobalConstNoOverload___at_____private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__1____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("Not implemented yet, [-builtin_simproc]", 39, 39);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663____boxed), 6, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_initFn___lam__1____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("Grind", 5, 5);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_5);
x_16 = l_Lean_Name_str___override(x_15, x_7);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = l_Lean_Name_str___override(x_18, x_9);
x_20 = lean_mk_string_unchecked("PropagatorAttr", 14, 14);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("_hyg", 4, 4);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_unsigned_to_nat(663u);
x_25 = l_Lean_Name_num___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("grindPropagatorBuiltinAttr", 26, 26);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("Builtin `grind` propagator procedure", 36, 36);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_3);
x_33 = l_Lean_registerBuiltinAttribute(x_32, x_1);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__1____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_initFn___lam__1____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedBuiltinPropagators = _init_l_Lean_Meta_Grind_instInhabitedBuiltinPropagators();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedBuiltinPropagators);
if (builtin) {res = l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_52_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_builtinPropagatorsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_builtinPropagatorsRef);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_PropagatorAttr___hyg_663_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
