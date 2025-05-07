// Lean compiler output
// Module: Init.MetaTypes
// Imports: Init.Core
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
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedNameGenerator;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedEtaStructMode;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences;
uint8_t l_List_hasDecEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instBEqConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_neutralConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_757_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedConfig;
LEAN_EXPORT uint8_t l_Lean_Meta_instInhabitedTransparencyMode;
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_757____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOccurrences;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqEtaStructMode;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedOccurrences;
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqTransparencyMode;
LEAN_EXPORT lean_object* l_Lean_Meta_DSimp_instInhabitedConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg___lam__0___boxed(lean_object*);
static lean_object* _init_l_Lean_instInhabitedNameGenerator() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx(uint8_t x_1) {
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_TransparencyMode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_TransparencyMode_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_TransparencyMode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TransparencyMode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_TransparencyMode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedTransparencyMode() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_TransparencyMode_toCtorIdx(x_1);
x_4 = l_Lean_Meta_TransparencyMode_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instBEqTransparencyMode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_MetaTypes_0__Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes___hyg_73____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_EtaStructMode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_TransparencyMode_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_EtaStructMode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_EtaStructMode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_EtaStructMode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_EtaStructMode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Meta_instInhabitedEtaStructMode() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_EtaStructMode_toCtorIdx(x_1);
x_4 = l_Lean_Meta_EtaStructMode_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instBEqEtaStructMode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DSimp_instInhabitedConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 0, 13);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 0, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 1, x_5);
x_6 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 2, x_6);
x_7 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, 3, x_7);
x_8 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 4, x_8);
x_9 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 5, x_9);
x_10 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 6, x_10);
x_11 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 7, x_11);
x_12 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 8, x_12);
x_13 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 9, x_13);
x_14 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 10, x_14);
x_15 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 11, x_15);
x_16 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, 12, x_16);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_31; uint8_t x_36; uint8_t x_41; uint8_t x_46; uint8_t x_51; uint8_t x_56; uint8_t x_61; lean_object* x_79; 
x_3 = lean_ctor_get_uint8(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, 1);
x_5 = lean_ctor_get_uint8(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, 3);
x_7 = lean_ctor_get_uint8(x_1, 4);
x_8 = lean_ctor_get_uint8(x_1, 5);
x_9 = lean_ctor_get_uint8(x_1, 6);
x_10 = lean_ctor_get_uint8(x_1, 7);
x_11 = lean_ctor_get_uint8(x_1, 8);
x_12 = lean_ctor_get_uint8(x_1, 9);
x_13 = lean_ctor_get_uint8(x_1, 10);
x_14 = lean_ctor_get_uint8(x_1, 11);
x_15 = lean_ctor_get_uint8(x_1, 12);
x_16 = lean_ctor_get_uint8(x_2, 0);
x_17 = lean_ctor_get_uint8(x_2, 1);
x_18 = lean_ctor_get_uint8(x_2, 2);
x_19 = lean_ctor_get_uint8(x_2, 3);
x_20 = lean_ctor_get_uint8(x_2, 4);
x_21 = lean_ctor_get_uint8(x_2, 5);
x_22 = lean_ctor_get_uint8(x_2, 6);
x_23 = lean_ctor_get_uint8(x_2, 7);
x_24 = lean_ctor_get_uint8(x_2, 8);
x_25 = lean_ctor_get_uint8(x_2, 9);
x_26 = lean_ctor_get_uint8(x_2, 10);
x_27 = lean_ctor_get_uint8(x_2, 11);
x_28 = lean_ctor_get_uint8(x_2, 12);
x_79 = lean_box(0);
if (x_3 == 0)
{
if (x_16 == 0)
{
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = lean_unbox(x_79);
return x_80;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_81; 
x_81 = lean_unbox(x_79);
return x_81;
}
else
{
goto block_78;
}
}
block_30:
{
if (x_15 == 0)
{
if (x_28 == 0)
{
return x_29;
}
else
{
return x_15;
}
}
else
{
return x_28;
}
}
block_35:
{
lean_object* x_32; 
x_32 = lean_box(0);
if (x_14 == 0)
{
if (x_27 == 0)
{
x_29 = x_31;
goto block_30;
}
else
{
uint8_t x_33; 
x_33 = lean_unbox(x_32);
return x_33;
}
}
else
{
if (x_27 == 0)
{
uint8_t x_34; 
x_34 = lean_unbox(x_32);
return x_34;
}
else
{
x_29 = x_31;
goto block_30;
}
}
}
block_40:
{
lean_object* x_37; 
x_37 = lean_box(0);
if (x_13 == 0)
{
if (x_26 == 0)
{
x_31 = x_36;
goto block_35;
}
else
{
uint8_t x_38; 
x_38 = lean_unbox(x_37);
return x_38;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_39; 
x_39 = lean_unbox(x_37);
return x_39;
}
else
{
x_31 = x_36;
goto block_35;
}
}
}
block_45:
{
lean_object* x_42; 
x_42 = lean_box(0);
if (x_12 == 0)
{
if (x_25 == 0)
{
x_36 = x_41;
goto block_40;
}
else
{
uint8_t x_43; 
x_43 = lean_unbox(x_42);
return x_43;
}
}
else
{
if (x_25 == 0)
{
uint8_t x_44; 
x_44 = lean_unbox(x_42);
return x_44;
}
else
{
x_36 = x_41;
goto block_40;
}
}
}
block_50:
{
lean_object* x_47; 
x_47 = lean_box(0);
if (x_11 == 0)
{
if (x_24 == 0)
{
x_41 = x_46;
goto block_45;
}
else
{
uint8_t x_48; 
x_48 = lean_unbox(x_47);
return x_48;
}
}
else
{
if (x_24 == 0)
{
uint8_t x_49; 
x_49 = lean_unbox(x_47);
return x_49;
}
else
{
x_41 = x_46;
goto block_45;
}
}
}
block_55:
{
lean_object* x_52; 
x_52 = lean_box(0);
if (x_10 == 0)
{
if (x_23 == 0)
{
x_46 = x_51;
goto block_50;
}
else
{
uint8_t x_53; 
x_53 = lean_unbox(x_52);
return x_53;
}
}
else
{
if (x_23 == 0)
{
uint8_t x_54; 
x_54 = lean_unbox(x_52);
return x_54;
}
else
{
x_46 = x_51;
goto block_50;
}
}
}
block_60:
{
lean_object* x_57; 
x_57 = lean_box(0);
if (x_9 == 0)
{
if (x_22 == 0)
{
x_51 = x_56;
goto block_55;
}
else
{
uint8_t x_58; 
x_58 = lean_unbox(x_57);
return x_58;
}
}
else
{
if (x_22 == 0)
{
uint8_t x_59; 
x_59 = lean_unbox(x_57);
return x_59;
}
else
{
x_51 = x_56;
goto block_55;
}
}
}
block_65:
{
if (x_61 == 0)
{
return x_61;
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
if (x_8 == 0)
{
if (x_21 == 0)
{
x_56 = x_61;
goto block_60;
}
else
{
uint8_t x_63; 
x_63 = lean_unbox(x_62);
return x_63;
}
}
else
{
if (x_21 == 0)
{
uint8_t x_64; 
x_64 = lean_unbox(x_62);
return x_64;
}
else
{
x_56 = x_61;
goto block_60;
}
}
}
}
block_70:
{
uint8_t x_66; 
x_66 = l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(x_6, x_19);
if (x_66 == 0)
{
return x_66;
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
if (x_7 == 0)
{
if (x_20 == 0)
{
x_61 = x_66;
goto block_65;
}
else
{
uint8_t x_68; 
x_68 = lean_unbox(x_67);
return x_68;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_69; 
x_69 = lean_unbox(x_67);
return x_69;
}
else
{
x_61 = x_66;
goto block_65;
}
}
}
}
block_74:
{
lean_object* x_71; 
x_71 = lean_box(0);
if (x_5 == 0)
{
if (x_18 == 0)
{
goto block_70;
}
else
{
uint8_t x_72; 
x_72 = lean_unbox(x_71);
return x_72;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_73; 
x_73 = lean_unbox(x_71);
return x_73;
}
else
{
goto block_70;
}
}
}
block_78:
{
lean_object* x_75; 
x_75 = lean_box(0);
if (x_4 == 0)
{
if (x_17 == 0)
{
goto block_74;
}
else
{
uint8_t x_76; 
x_76 = lean_unbox(x_75);
return x_76;
}
}
else
{
if (x_17 == 0)
{
uint8_t x_77; 
x_77 = lean_unbox(x_75);
return x_77;
}
else
{
goto block_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_MetaTypes_0__Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_DSimp_instBEqConfig() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_MetaTypes_0__Lean_Meta_DSimp_beqConfig____x40_Init_MetaTypes___hyg_268____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_defaultMaxSteps() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(100000u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_6);
x_7 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 3, x_8);
x_9 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 4, x_9);
x_10 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 5, x_10);
x_11 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 6, x_11);
x_12 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 7, x_12);
x_13 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 8, x_13);
x_14 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 9, x_14);
x_15 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 10, x_15);
x_16 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 11, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 12, x_17);
x_18 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 13, x_18);
x_19 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 14, x_19);
x_20 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 15, x_20);
x_21 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 16, x_21);
x_22 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 17, x_22);
x_23 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 18, x_23);
x_24 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 19, x_24);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_757_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_49; uint8_t x_54; uint8_t x_59; uint8_t x_64; uint8_t x_69; uint8_t x_74; uint8_t x_79; uint8_t x_84; uint8_t x_89; uint8_t x_94; uint8_t x_99; uint8_t x_125; uint8_t x_130; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 5);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 9);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 10);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 11);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 12);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 13);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 14);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 15);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 17);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 18);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 4);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 5);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 6);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 7);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 8);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 9);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 10);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 11);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 12);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 13);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 14);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 15);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 16);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 17);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 18);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 19);
x_130 = lean_nat_dec_eq(x_3, x_25);
if (x_130 == 0)
{
return x_130;
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_eq(x_4, x_26);
if (x_131 == 0)
{
return x_131;
}
else
{
lean_object* x_132; 
x_132 = lean_box(0);
if (x_5 == 0)
{
if (x_27 == 0)
{
x_125 = x_131;
goto block_129;
}
else
{
uint8_t x_133; 
x_133 = lean_unbox(x_132);
return x_133;
}
}
else
{
if (x_27 == 0)
{
uint8_t x_134; 
x_134 = lean_unbox(x_132);
return x_134;
}
else
{
x_125 = x_131;
goto block_129;
}
}
}
}
block_48:
{
if (x_24 == 0)
{
if (x_46 == 0)
{
return x_47;
}
else
{
return x_24;
}
}
else
{
return x_46;
}
}
block_53:
{
lean_object* x_50; 
x_50 = lean_box(0);
if (x_23 == 0)
{
if (x_45 == 0)
{
x_47 = x_49;
goto block_48;
}
else
{
uint8_t x_51; 
x_51 = lean_unbox(x_50);
return x_51;
}
}
else
{
if (x_45 == 0)
{
uint8_t x_52; 
x_52 = lean_unbox(x_50);
return x_52;
}
else
{
x_47 = x_49;
goto block_48;
}
}
}
block_58:
{
lean_object* x_55; 
x_55 = lean_box(0);
if (x_22 == 0)
{
if (x_44 == 0)
{
x_49 = x_54;
goto block_53;
}
else
{
uint8_t x_56; 
x_56 = lean_unbox(x_55);
return x_56;
}
}
else
{
if (x_44 == 0)
{
uint8_t x_57; 
x_57 = lean_unbox(x_55);
return x_57;
}
else
{
x_49 = x_54;
goto block_53;
}
}
}
block_63:
{
lean_object* x_60; 
x_60 = lean_box(0);
if (x_21 == 0)
{
if (x_43 == 0)
{
x_54 = x_59;
goto block_58;
}
else
{
uint8_t x_61; 
x_61 = lean_unbox(x_60);
return x_61;
}
}
else
{
if (x_43 == 0)
{
uint8_t x_62; 
x_62 = lean_unbox(x_60);
return x_62;
}
else
{
x_54 = x_59;
goto block_58;
}
}
}
block_68:
{
lean_object* x_65; 
x_65 = lean_box(0);
if (x_20 == 0)
{
if (x_42 == 0)
{
x_59 = x_64;
goto block_63;
}
else
{
uint8_t x_66; 
x_66 = lean_unbox(x_65);
return x_66;
}
}
else
{
if (x_42 == 0)
{
uint8_t x_67; 
x_67 = lean_unbox(x_65);
return x_67;
}
else
{
x_59 = x_64;
goto block_63;
}
}
}
block_73:
{
lean_object* x_70; 
x_70 = lean_box(0);
if (x_19 == 0)
{
if (x_41 == 0)
{
x_64 = x_69;
goto block_68;
}
else
{
uint8_t x_71; 
x_71 = lean_unbox(x_70);
return x_71;
}
}
else
{
if (x_41 == 0)
{
uint8_t x_72; 
x_72 = lean_unbox(x_70);
return x_72;
}
else
{
x_64 = x_69;
goto block_68;
}
}
}
block_78:
{
lean_object* x_75; 
x_75 = lean_box(0);
if (x_18 == 0)
{
if (x_40 == 0)
{
x_69 = x_74;
goto block_73;
}
else
{
uint8_t x_76; 
x_76 = lean_unbox(x_75);
return x_76;
}
}
else
{
if (x_40 == 0)
{
uint8_t x_77; 
x_77 = lean_unbox(x_75);
return x_77;
}
else
{
x_69 = x_74;
goto block_73;
}
}
}
block_83:
{
lean_object* x_80; 
x_80 = lean_box(0);
if (x_17 == 0)
{
if (x_39 == 0)
{
x_74 = x_79;
goto block_78;
}
else
{
uint8_t x_81; 
x_81 = lean_unbox(x_80);
return x_81;
}
}
else
{
if (x_39 == 0)
{
uint8_t x_82; 
x_82 = lean_unbox(x_80);
return x_82;
}
else
{
x_74 = x_79;
goto block_78;
}
}
}
block_88:
{
lean_object* x_85; 
x_85 = lean_box(0);
if (x_16 == 0)
{
if (x_38 == 0)
{
x_79 = x_84;
goto block_83;
}
else
{
uint8_t x_86; 
x_86 = lean_unbox(x_85);
return x_86;
}
}
else
{
if (x_38 == 0)
{
uint8_t x_87; 
x_87 = lean_unbox(x_85);
return x_87;
}
else
{
x_79 = x_84;
goto block_83;
}
}
}
block_93:
{
lean_object* x_90; 
x_90 = lean_box(0);
if (x_15 == 0)
{
if (x_37 == 0)
{
x_84 = x_89;
goto block_88;
}
else
{
uint8_t x_91; 
x_91 = lean_unbox(x_90);
return x_91;
}
}
else
{
if (x_37 == 0)
{
uint8_t x_92; 
x_92 = lean_unbox(x_90);
return x_92;
}
else
{
x_84 = x_89;
goto block_88;
}
}
}
block_98:
{
lean_object* x_95; 
x_95 = lean_box(0);
if (x_14 == 0)
{
if (x_36 == 0)
{
x_89 = x_94;
goto block_93;
}
else
{
uint8_t x_96; 
x_96 = lean_unbox(x_95);
return x_96;
}
}
else
{
if (x_36 == 0)
{
uint8_t x_97; 
x_97 = lean_unbox(x_95);
return x_97;
}
else
{
x_89 = x_94;
goto block_93;
}
}
}
block_103:
{
if (x_99 == 0)
{
return x_99;
}
else
{
lean_object* x_100; 
x_100 = lean_box(0);
if (x_13 == 0)
{
if (x_35 == 0)
{
x_94 = x_99;
goto block_98;
}
else
{
uint8_t x_101; 
x_101 = lean_unbox(x_100);
return x_101;
}
}
else
{
if (x_35 == 0)
{
uint8_t x_102; 
x_102 = lean_unbox(x_100);
return x_102;
}
else
{
x_94 = x_99;
goto block_98;
}
}
}
}
block_108:
{
uint8_t x_104; 
x_104 = l___private_Init_MetaTypes_0__Lean_Meta_beqEtaStructMode____x40_Init_MetaTypes___hyg_106_(x_11, x_33);
if (x_104 == 0)
{
return x_104;
}
else
{
lean_object* x_105; 
x_105 = lean_box(0);
if (x_12 == 0)
{
if (x_34 == 0)
{
x_99 = x_104;
goto block_103;
}
else
{
uint8_t x_106; 
x_106 = lean_unbox(x_105);
return x_106;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_107; 
x_107 = lean_unbox(x_105);
return x_107;
}
else
{
x_99 = x_104;
goto block_103;
}
}
}
}
block_112:
{
lean_object* x_109; 
x_109 = lean_box(0);
if (x_10 == 0)
{
if (x_32 == 0)
{
goto block_108;
}
else
{
uint8_t x_110; 
x_110 = lean_unbox(x_109);
return x_110;
}
}
else
{
if (x_32 == 0)
{
uint8_t x_111; 
x_111 = lean_unbox(x_109);
return x_111;
}
else
{
goto block_108;
}
}
}
block_116:
{
lean_object* x_113; 
x_113 = lean_box(0);
if (x_9 == 0)
{
if (x_31 == 0)
{
goto block_112;
}
else
{
uint8_t x_114; 
x_114 = lean_unbox(x_113);
return x_114;
}
}
else
{
if (x_31 == 0)
{
uint8_t x_115; 
x_115 = lean_unbox(x_113);
return x_115;
}
else
{
goto block_112;
}
}
}
block_120:
{
lean_object* x_117; 
x_117 = lean_box(0);
if (x_8 == 0)
{
if (x_30 == 0)
{
goto block_116;
}
else
{
uint8_t x_118; 
x_118 = lean_unbox(x_117);
return x_118;
}
}
else
{
if (x_30 == 0)
{
uint8_t x_119; 
x_119 = lean_unbox(x_117);
return x_119;
}
else
{
goto block_116;
}
}
}
block_124:
{
lean_object* x_121; 
x_121 = lean_box(0);
if (x_7 == 0)
{
if (x_29 == 0)
{
goto block_120;
}
else
{
uint8_t x_122; 
x_122 = lean_unbox(x_121);
return x_122;
}
}
else
{
if (x_29 == 0)
{
uint8_t x_123; 
x_123 = lean_unbox(x_121);
return x_123;
}
else
{
goto block_120;
}
}
}
block_129:
{
if (x_125 == 0)
{
return x_125;
}
else
{
lean_object* x_126; 
x_126 = lean_box(0);
if (x_6 == 0)
{
if (x_28 == 0)
{
goto block_124;
}
else
{
uint8_t x_127; 
x_127 = lean_unbox(x_126);
return x_127;
}
}
else
{
if (x_28 == 0)
{
uint8_t x_128; 
x_128 = lean_unbox(x_126);
return x_128;
}
else
{
goto block_124;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_757____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_MetaTypes_0__Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_757_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instBEqConfig() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_MetaTypes_0__Lean_Meta_Simp_beqConfig____x40_Init_MetaTypes___hyg_757____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_neutralConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_1 = lean_unsigned_to_nat(100000u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_box(0);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_7);
x_8 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_8);
x_9 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_9);
x_10 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_10);
x_11 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_11);
x_12 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_12);
x_13 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_13);
x_14 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_14);
x_15 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_16);
x_17 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_17);
x_18 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_18);
x_19 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_19);
x_20 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_20);
x_21 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_21);
x_22 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_22);
x_23 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_23);
x_24 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_24);
x_25 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_25);
x_26 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 19, x_26);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedOccurrences() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_3 = x_12;
x_4 = x_13;
goto block_7;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_3 = x_16;
x_4 = x_17;
goto block_7;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
block_7:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_6 = l_List_hasDecEq___redArg(x_5, x_3, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instBEqOccurrences() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instCoeListNatOccurrences___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instCoeListNatOccurrences() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instCoeListNatOccurrences___lam__0), 1, 0);
return x_1;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_MetaTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedNameGenerator = _init_l_Lean_instInhabitedNameGenerator();
lean_mark_persistent(l_Lean_instInhabitedNameGenerator);
l_Lean_Meta_instInhabitedTransparencyMode = _init_l_Lean_Meta_instInhabitedTransparencyMode();
l_Lean_Meta_instBEqTransparencyMode = _init_l_Lean_Meta_instBEqTransparencyMode();
lean_mark_persistent(l_Lean_Meta_instBEqTransparencyMode);
l_Lean_Meta_instInhabitedEtaStructMode = _init_l_Lean_Meta_instInhabitedEtaStructMode();
l_Lean_Meta_instBEqEtaStructMode = _init_l_Lean_Meta_instBEqEtaStructMode();
lean_mark_persistent(l_Lean_Meta_instBEqEtaStructMode);
l_Lean_Meta_DSimp_instInhabitedConfig = _init_l_Lean_Meta_DSimp_instInhabitedConfig();
lean_mark_persistent(l_Lean_Meta_DSimp_instInhabitedConfig);
l_Lean_Meta_DSimp_instBEqConfig = _init_l_Lean_Meta_DSimp_instBEqConfig();
lean_mark_persistent(l_Lean_Meta_DSimp_instBEqConfig);
l_Lean_Meta_Simp_defaultMaxSteps = _init_l_Lean_Meta_Simp_defaultMaxSteps();
lean_mark_persistent(l_Lean_Meta_Simp_defaultMaxSteps);
l_Lean_Meta_Simp_instInhabitedConfig = _init_l_Lean_Meta_Simp_instInhabitedConfig();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedConfig);
l_Lean_Meta_Simp_instBEqConfig = _init_l_Lean_Meta_Simp_instBEqConfig();
lean_mark_persistent(l_Lean_Meta_Simp_instBEqConfig);
l_Lean_Meta_Simp_neutralConfig = _init_l_Lean_Meta_Simp_neutralConfig();
lean_mark_persistent(l_Lean_Meta_Simp_neutralConfig);
l_Lean_Meta_instInhabitedOccurrences = _init_l_Lean_Meta_instInhabitedOccurrences();
lean_mark_persistent(l_Lean_Meta_instInhabitedOccurrences);
l_Lean_Meta_instBEqOccurrences = _init_l_Lean_Meta_instBEqOccurrences();
lean_mark_persistent(l_Lean_Meta_instBEqOccurrences);
l_Lean_Meta_instCoeListNatOccurrences = _init_l_Lean_Meta_instCoeListNatOccurrences();
lean_mark_persistent(l_Lean_Meta_instCoeListNatOccurrences);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
