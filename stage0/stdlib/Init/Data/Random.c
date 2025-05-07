// Lean compiler output
// Module: Init.Data.Random
// Imports: Init.System.IO
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
LEAN_EXPORT lean_object* l_mkStdGen___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_rand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_stdGenRef;
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randBool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Init_Data_Random___hyg_765_(lean_object*);
LEAN_EXPORT lean_object* l_randBool___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_instReprStdGen;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___IO_rand_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen;
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___randNat___at___IO_rand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_stdRange;
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___randNat___at___IO_rand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_stdNext(lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___IO_rand_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedStdGen;
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_stdSplit(lean_object*);
LEAN_EXPORT lean_object* l_mkStdGen(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* _init_l_instInhabitedStdGen() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_stdRange() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(2147483562u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_mk_string_unchecked("⟨", 3, 1);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked(", ", 2, 2);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_8);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("⟩", 3, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_6);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = lean_mk_string_unchecked("⟨", 3, 1);
x_28 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_mk_string_unchecked(", ", 2, 2);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("⟩", 3, 1);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_27);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
return x_45;
}
}
}
static lean_object* _init_l_instReprStdGen() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instReprStdGen___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprStdGen___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_stdNext(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_64; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(53668u);
x_27 = lean_nat_div(x_24, x_26);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_unsigned_to_nat(40014u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_nat_to_int(x_24);
x_32 = lean_nat_to_int(x_26);
x_33 = lean_int_mul(x_28, x_32);
lean_dec(x_32);
x_34 = lean_int_sub(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
x_35 = lean_int_mul(x_30, x_34);
lean_dec(x_34);
lean_dec(x_30);
x_36 = lean_unsigned_to_nat(12211u);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_int_mul(x_28, x_37);
lean_dec(x_37);
lean_dec(x_28);
x_39 = lean_int_sub(x_35, x_38);
lean_dec(x_38);
lean_dec(x_35);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_to_int(x_40);
x_64 = lean_int_dec_lt(x_39, x_41);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Int_toNat(x_39);
lean_dec(x_39);
x_42 = x_65;
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_unsigned_to_nat(2147483563u);
x_67 = lean_nat_to_int(x_66);
x_68 = lean_int_add(x_39, x_67);
lean_dec(x_67);
lean_dec(x_39);
x_69 = l_Int_toNat(x_68);
lean_dec(x_68);
x_42 = x_69;
goto block_63;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
block_23:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_8);
x_10 = lean_nat_to_int(x_8);
lean_inc(x_9);
x_11 = lean_nat_to_int(x_9);
x_12 = lean_int_sub(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_dec_lt(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Int_toNat(x_12);
lean_dec(x_12);
x_17 = lean_unsigned_to_nat(2147483562u);
x_18 = lean_nat_mod(x_16, x_17);
lean_dec(x_16);
x_2 = x_8;
x_3 = x_9;
x_4 = x_18;
goto block_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(2147483562u);
x_20 = lean_nat_to_int(x_19);
x_21 = lean_int_add(x_12, x_20);
lean_dec(x_20);
lean_dec(x_12);
x_22 = l_Int_toNat(x_21);
lean_dec(x_21);
x_2 = x_8;
x_3 = x_9;
x_4 = x_22;
goto block_7;
}
}
block_63:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_43 = lean_unsigned_to_nat(52774u);
x_44 = lean_nat_div(x_25, x_43);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_unsigned_to_nat(40692u);
x_47 = lean_nat_to_int(x_46);
x_48 = lean_nat_to_int(x_25);
x_49 = lean_nat_to_int(x_43);
x_50 = lean_int_mul(x_45, x_49);
lean_dec(x_49);
x_51 = lean_int_sub(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
x_52 = lean_int_mul(x_47, x_51);
lean_dec(x_51);
lean_dec(x_47);
x_53 = lean_unsigned_to_nat(3791u);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_int_mul(x_45, x_54);
lean_dec(x_54);
lean_dec(x_45);
x_56 = lean_int_sub(x_52, x_55);
lean_dec(x_55);
lean_dec(x_52);
x_57 = lean_int_dec_lt(x_56, x_41);
lean_dec(x_41);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = l_Int_toNat(x_56);
lean_dec(x_56);
x_8 = x_42;
x_9 = x_58;
goto block_23;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_unsigned_to_nat(2147483399u);
x_60 = lean_nat_to_int(x_59);
x_61 = lean_int_add(x_56, x_60);
lean_dec(x_60);
lean_dec(x_56);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_8 = x_42;
x_9 = x_62;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_stdSplit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_20 = lean_unsigned_to_nat(2147483562u);
x_21 = lean_nat_dec_eq(x_12, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_12, x_22);
lean_dec(x_12);
x_14 = x_23;
goto block_19;
}
else
{
lean_object* x_24; 
lean_dec(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_14 = x_24;
goto block_19;
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_stdNext(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
block_19:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_eq(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
x_2 = x_14;
x_3 = x_17;
goto block_11;
}
else
{
lean_object* x_18; 
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(2147483398u);
x_2 = x_14;
x_3 = x_18;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_stdRange;
return x_2;
}
}
static lean_object* _init_l_instRandomGenStdGen() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_instRandomGenStdGen___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_stdNext), 1, 0);
x_3 = lean_alloc_closure((void*)(l_stdSplit), 1, 0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instRandomGenStdGen___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_mkStdGen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(2147483562u);
x_3 = lean_nat_div(x_1, x_2);
x_4 = lean_nat_mod(x_1, x_2);
x_5 = lean_unsigned_to_nat(2147483398u);
x_6 = lean_nat_mod(x_3, x_5);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
x_9 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_mkStdGen___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkStdGen(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 1)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_apply_1(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_nat_mul(x_8, x_3);
lean_dec(x_8);
x_15 = lean_nat_sub(x_13, x_2);
lean_dec(x_13);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_nat_div(x_4, x_3);
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_11, 0, x_16);
x_4 = x_19;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_nat_mul(x_8, x_3);
lean_dec(x_8);
x_24 = lean_nat_sub(x_21, x_2);
lean_dec(x_21);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_nat_div(x_4, x_3);
lean_dec(x_4);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_26, x_27);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_22);
x_4 = x_28;
x_5 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Random_0__randNatAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Random_0__randNatAux___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Random_0__randNatAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_randNat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_49; lean_object* x_50; 
x_49 = lean_nat_dec_lt(x_4, x_3);
if (x_49 == 0)
{
x_50 = x_3;
goto block_51;
}
else
{
x_50 = x_4;
goto block_51;
}
block_48:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_inc(x_2);
x_8 = lean_apply_1(x_7, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_nat_sub(x_11, x_10);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1000u);
x_16 = lean_nat_sub(x_6, x_5);
x_17 = lean_nat_add(x_16, x_13);
lean_dec(x_16);
x_18 = lean_nat_mul(x_17, x_15);
x_19 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_19);
x_20 = l___private_Init_Data_Random_0__randNatAux___redArg(x_1, x_10, x_14, x_18, x_8);
lean_dec(x_14);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_nat_mod(x_22, x_17);
lean_dec(x_17);
lean_dec(x_22);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_nat_mod(x_25, x_17);
lean_dec(x_17);
lean_dec(x_25);
x_28 = lean_nat_add(x_5, x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_nat_sub(x_31, x_30);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_32, x_33);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1000u);
x_36 = lean_nat_sub(x_6, x_5);
x_37 = lean_nat_add(x_36, x_33);
lean_dec(x_36);
x_38 = lean_nat_mul(x_37, x_35);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_2);
x_41 = l___private_Init_Data_Random_0__randNatAux___redArg(x_1, x_30, x_34, x_38, x_40);
lean_dec(x_34);
lean_dec(x_30);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_nat_mod(x_42, x_37);
lean_dec(x_37);
lean_dec(x_42);
x_46 = lean_nat_add(x_5, x_45);
lean_dec(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
block_51:
{
if (x_49 == 0)
{
x_5 = x_50;
x_6 = x_4;
goto block_48;
}
else
{
x_5 = x_50;
x_6 = x_3;
goto block_48;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_randNat___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_randNat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_randNat___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_randNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_randNat(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_randBool___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_randNat___redArg(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_nat_dec_eq(x_7, x_4);
lean_dec(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_nat_dec_eq(x_10, x_4);
lean_dec(x_10);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_randBool(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_randBool___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Init_Data_Random___hyg_765_(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_usize_of_nat(x_2);
x_4 = lean_io_get_random_bytes(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_ByteArray_toUInt64LE_x21(x_5);
lean_dec(x_5);
x_8 = lean_uint64_to_nat(x_7);
x_9 = l_mkStdGen(x_8);
lean_dec(x_8);
x_10 = lean_st_mk_ref(x_9, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_IO_stdGenRef;
x_4 = l_mkStdGen(x_1);
x_5 = lean_st_ref_set(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_setRandSeed(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___randNat___at___IO_rand_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 1)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_stdNext(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_nat_mul(x_7, x_2);
lean_dec(x_7);
x_13 = lean_nat_sub(x_11, x_1);
lean_dec(x_11);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_nat_div(x_3, x_2);
lean_dec(x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_14);
x_3 = x_17;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_nat_mul(x_7, x_2);
lean_dec(x_7);
x_22 = lean_nat_sub(x_19, x_1);
lean_dec(x_19);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_nat_div(x_3, x_2);
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_20);
x_3 = x_26;
x_4 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at___IO_rand_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_47; lean_object* x_48; 
x_47 = lean_nat_dec_lt(x_3, x_2);
if (x_47 == 0)
{
x_48 = x_2;
goto block_49;
}
else
{
x_48 = x_3;
goto block_49;
}
block_46:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_stdRange;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1000u);
x_14 = lean_nat_sub(x_5, x_4);
x_15 = lean_nat_add(x_14, x_11);
lean_dec(x_14);
x_16 = lean_nat_mul(x_15, x_13);
x_17 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_17);
x_18 = l___private_Init_Data_Random_0__randNatAux___at___randNat___at___IO_rand_spec__0_spec__0(x_8, x_12, x_16, x_6);
lean_dec(x_12);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_nat_mod(x_20, x_15);
lean_dec(x_15);
lean_dec(x_20);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_nat_mod(x_23, x_15);
lean_dec(x_15);
lean_dec(x_23);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_6);
x_30 = lean_nat_sub(x_29, x_28);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_30, x_31);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1000u);
x_34 = lean_nat_sub(x_5, x_4);
x_35 = lean_nat_add(x_34, x_31);
lean_dec(x_34);
x_36 = lean_nat_mul(x_35, x_33);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
x_39 = l___private_Init_Data_Random_0__randNatAux___at___randNat___at___IO_rand_spec__0_spec__0(x_28, x_32, x_36, x_38);
lean_dec(x_32);
lean_dec(x_28);
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
x_43 = lean_nat_mod(x_40, x_35);
lean_dec(x_35);
lean_dec(x_40);
x_44 = lean_nat_add(x_4, x_43);
lean_dec(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
block_49:
{
if (x_47 == 0)
{
x_4 = x_48;
x_5 = x_3;
goto block_46;
}
else
{
x_4 = x_48;
x_5 = x_2;
goto block_46;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_rand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = l_IO_stdGenRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_randNat___at___IO_rand_spec__0(x_6, x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_set(x_4, x_10, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___randNat___at___IO_rand_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Random_0__randNatAux___at___randNat___at___IO_rand_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_randNat___at___IO_rand_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_randNat___at___IO_rand_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_rand(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Random(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedStdGen = _init_l_instInhabitedStdGen();
lean_mark_persistent(l_instInhabitedStdGen);
l_stdRange = _init_l_stdRange();
lean_mark_persistent(l_stdRange);
l_instReprStdGen = _init_l_instReprStdGen();
lean_mark_persistent(l_instReprStdGen);
l_instRandomGenStdGen = _init_l_instRandomGenStdGen();
lean_mark_persistent(l_instRandomGenStdGen);
res = l_initFn____x40_Init_Data_Random___hyg_765_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_IO_stdGenRef = lean_io_result_get_value(res);
lean_mark_persistent(l_IO_stdGenRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
