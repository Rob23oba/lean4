// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndInfo
// Imports: Lean.Meta.Basic Lean.ScopedEnvExtension Lean.ReservedNameAction
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedFunIndParamKind;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFunIndInfo;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg(uint8_t, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__1____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_setFunIndInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_funIndInfoExt;
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__1____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqFunIndParamKind;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprFunIndParamKind;
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_FunIndParamKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_FunIndParamKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_FunIndParamKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_FunIndParamKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_FunIndParamKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FunIndParamKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_FunIndParamKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_FunIndParamKind_toCtorIdx(x_1);
x_4 = l_Lean_Meta_FunIndParamKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instBEqFunIndParamKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_beqFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_10____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; 
switch (x_1) {
case 0:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(1024u);
x_31 = lean_nat_dec_le(x_30, x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_to_int(x_32);
x_3 = x_33;
goto block_11;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_to_int(x_34);
x_3 = x_35;
goto block_11;
}
}
case 1:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(1024u);
x_37 = lean_nat_dec_le(x_36, x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_to_int(x_38);
x_12 = x_39;
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_to_int(x_40);
x_12 = x_41;
goto block_20;
}
}
default: 
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(1024u);
x_43 = lean_nat_dec_le(x_42, x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(2u);
x_45 = lean_nat_to_int(x_44);
x_21 = x_45;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_to_int(x_46);
x_21 = x_47;
goto block_29;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Meta.FunIndParamKind.dropped", 33, 33);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.Meta.FunIndParamKind.param", 31, 31);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.Meta.FunIndParamKind.target", 32, 32);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndParamKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28____boxed), 2, 0);
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedFunIndParamKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedFunIndInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_empty(lean_box(0));
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndParamKind____x40_Lean_Meta_Tactic_FunIndInfo___hyg_28_(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__1____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("false", 5, 5);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("true", 4, 4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("funIndName", 10, 10);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(14u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_Name_reprPrec(x_12, x_13);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(0);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_16);
x_37 = lean_unbox(x_17);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_mk_string_unchecked(",", 1, 1);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_40);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked("levelMask", 9, 9);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_8);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
x_48 = lean_unsigned_to_nat(13u);
x_49 = lean_nat_to_int(x_48);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
x_83 = lean_array_get_size(x_82);
x_84 = lean_nat_dec_eq(x_83, x_13);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_85 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__1____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed), 1, 0);
x_86 = lean_mk_string_unchecked("#[", 2, 2);
x_87 = lean_array_to_list(x_82);
lean_inc(x_40);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_40);
lean_ctor_set(x_88, 1, x_42);
x_89 = l_Std_Format_joinSep(lean_box(0), x_85, x_87, x_88);
x_90 = lean_mk_string_unchecked("]", 1, 1);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_to_int(x_91);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_86);
x_94 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Std_Format_fill(x_97);
x_50 = x_98;
goto block_81;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_82);
x_99 = lean_mk_string_unchecked("#[]", 3, 3);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_50 = x_100;
goto block_81;
}
block_35:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unbox(x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_mk_string_unchecked(" }", 2, 2);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_to_int(x_26);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_unbox(x_17);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
block_81:
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_unbox(x_17);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_52);
lean_inc(x_40);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_40);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
x_57 = lean_mk_string_unchecked("params", 6, 6);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
x_61 = lean_unsigned_to_nat(10u);
x_62 = lean_nat_to_int(x_61);
x_63 = lean_ctor_get(x_1, 2);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_eq(x_64, x_13);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_mk_string_unchecked("#[", 2, 2);
x_67 = lean_array_to_list(x_63);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_42);
x_69 = l_Std_Format_joinSep(lean_box(0), x_14, x_67, x_68);
x_70 = lean_mk_string_unchecked("]", 1, 1);
x_71 = lean_unsigned_to_nat(2u);
x_72 = lean_nat_to_int(x_71);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_66);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Std_Format_fill(x_77);
x_18 = x_62;
x_19 = x_60;
x_20 = x_78;
goto block_35;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_63);
lean_dec(x_40);
lean_dec(x_14);
x_79 = lean_mk_string_unchecked("#[]", 3, 3);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_18 = x_62;
x_19 = x_60;
x_20 = x_80;
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__1____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo___redArg___lam__1____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprFunIndInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_reprFunIndInfo____x40_Lean_Meta_Tactic_FunIndInfo___hyg_195____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Meta", 4, 4);
x_5 = lean_mk_string_unchecked("funIndInfoExt", 13, 13);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = l_Lean_mkMapDeclarationExtension___redArg(x_6, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("induct", 6, 6);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_Name_append(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("induct_unfolding", 16, 16);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Name_append(x_1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInductName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_getFunInductName(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("fun_cases", 9, 9);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_Name_append(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("fun_cases_unfolding", 19, 19);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Name_append(x_1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunCasesName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_getFunCasesName(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("mutual_induct", 13, 13);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_Name_append(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_mk_string_unchecked("mutual_induct_unfolding", 23, 23);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Name_append(x_1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMutualInductName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_getMutualInductName(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_12; 
lean_inc(x_2);
x_12 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
if (lean_obj_tag(x_14) == 1)
{
lean_free_object(x_12);
lean_dec(x_14);
if (x_1 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Meta_getFunInductName(x_2, x_1);
x_16 = x_36;
goto block_35;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Meta_getFunCasesName(x_2, x_38);
x_16 = x_39;
goto block_35;
}
}
else
{
lean_object* x_40; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
lean_ctor_set(x_12, 0, x_40);
return x_12;
}
block_35:
{
lean_object* x_17; 
x_17 = l_Lean_realizeGlobalConstNoOverloadCore(x_16, x_3, x_4, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
lean_dec(x_26);
x_6 = x_17;
x_7 = x_27;
x_8 = x_29;
goto block_11;
}
else
{
lean_dec(x_26);
x_6 = x_17;
x_7 = x_27;
x_8 = x_28;
goto block_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
lean_inc(x_31);
lean_inc(x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Exception_isInterrupt(x_30);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Exception_isRuntime(x_30);
lean_dec(x_30);
x_6 = x_32;
x_7 = x_31;
x_8 = x_34;
goto block_11;
}
else
{
lean_dec(x_30);
x_6 = x_32;
x_7 = x_31;
x_8 = x_33;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
if (lean_obj_tag(x_41) == 1)
{
lean_dec(x_41);
if (x_1 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_Meta_getFunInductName(x_2, x_1);
x_43 = x_57;
goto block_56;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_58 = lean_box(0);
x_59 = lean_unbox(x_58);
x_60 = l_Lean_Meta_getFunCasesName(x_2, x_59);
x_43 = x_60;
goto block_56;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_42);
return x_62;
}
block_56:
{
lean_object* x_44; 
x_44 = l_Lean_realizeGlobalConstNoOverloadCore(x_43, x_3, x_4, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
lean_inc(x_51);
lean_inc(x_50);
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Exception_isInterrupt(x_50);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Exception_isRuntime(x_50);
lean_dec(x_50);
x_6 = x_53;
x_7 = x_51;
x_8 = x_55;
goto block_11;
}
else
{
lean_dec(x_50);
x_6 = x_53;
x_7 = x_51;
x_8 = x_54;
goto block_11;
}
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_12);
if (x_63 == 0)
{
return x_12;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_12, 0);
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_12);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
block_11:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_dec(x_7);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunInduct_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_getFunInduct_x3f(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_setFunIndInfo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instInhabitedCoreM___lam__0___boxed), 3, 0);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setFunIndInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_instInhabitedFunIndInfo;
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Meta_funIndInfoExt;
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_11);
x_12 = l_Lean_MapDeclarationExtension_contains___redArg(x_8, x_10, x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
x_13 = lean_st_ref_take(x_3, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_10, x_17, x_11, x_1);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 3);
lean_inc(x_21);
x_22 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_23);
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_23);
x_24 = lean_ctor_get(x_15, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 6);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 7);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_13);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_16);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_10, x_37, x_11, x_1);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 3);
lean_inc(x_41);
x_42 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_ctor_get(x_35, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 7);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_44);
lean_ctor_set(x_48, 5, x_45);
lean_ctor_set(x_48, 6, x_46);
lean_ctor_set(x_48, 7, x_47);
x_49 = lean_st_ref_set(x_3, x_48, x_36);
lean_dec(x_3);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
lean_dec(x_1);
x_54 = lean_mk_string_unchecked("Lean.Meta.Tactic.FunIndInfo", 27, 27);
x_55 = lean_mk_string_unchecked("Lean.Meta.setFunIndInfo", 23, 23);
x_56 = lean_unsigned_to_nat(75u);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_mk_string_unchecked("assertion violation: !(funIndInfoExt.contains ( __do_lift._@.Lean.Meta.Tactic.FunIndInfo._hyg.500.0 ) funIndInfo.funIndName)\n  ", 127, 127);
x_59 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_54, x_55, x_56, x_57, x_58);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
x_60 = l_panic___at___Lean_Meta_setFunIndInfo_spec__0(x_59, x_2, x_3, x_7);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Meta_instInhabitedFunIndInfo;
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_funIndInfoExt;
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_7, x_9, x_8, x_1, x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = l_Lean_Meta_instInhabitedFunIndInfo;
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_funIndInfoExt;
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_15, x_17, x_16, x_1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getFunIndInfoForInduct_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Meta_getFunInduct_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(x_15, x_4, x_14);
lean_dec(x_4);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getFunIndInfo_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Meta_getFunIndInfo_x3f(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FunIndInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instBEqFunIndParamKind = _init_l_Lean_Meta_instBEqFunIndParamKind();
lean_mark_persistent(l_Lean_Meta_instBEqFunIndParamKind);
l_Lean_Meta_instReprFunIndParamKind = _init_l_Lean_Meta_instReprFunIndParamKind();
lean_mark_persistent(l_Lean_Meta_instReprFunIndParamKind);
l_Lean_Meta_instInhabitedFunIndParamKind = _init_l_Lean_Meta_instInhabitedFunIndParamKind();
l_Lean_Meta_instInhabitedFunIndInfo = _init_l_Lean_Meta_instInhabitedFunIndInfo();
lean_mark_persistent(l_Lean_Meta_instInhabitedFunIndInfo);
l_Lean_Meta_instReprFunIndInfo = _init_l_Lean_Meta_instReprFunIndInfo();
lean_mark_persistent(l_Lean_Meta_instReprFunIndInfo);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_FunIndInfo___hyg_273_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_funIndInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_funIndInfoExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
