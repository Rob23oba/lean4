// Lean compiler output
// Module: Std.Time.Zoned.Offset
// Imports: Std.Time.Time
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
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187_(lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_decEqOffset____x40_Std_Time_Zoned_Offset___hyg_225_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset;
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_zero;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours___boxed(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_Time_Second_instOrdOffset;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset;
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_decEqOffset____x40_Std_Time_Zoned_Offset___hyg_225____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset____x40_Std_Time_Zoned_Offset___hyg_187____boxed(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset____x40_Std_Time_Zoned_Offset___hyg_187_(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("second", 6, 6);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(10u);
x_11 = lean_nat_to_int(x_10);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_int_dec_lt(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Int_repr(x_1);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_12 = x_33;
goto block_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Int_repr(x_1);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Repr_addAppParen(x_35, x_29);
x_12 = x_36;
goto block_28;
}
block_28:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_mk_string_unchecked(" }", 2, 2);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_to_int(x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unbox(x_14);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset____x40_Std_Time_Zoned_Offset___hyg_187_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset____x40_Std_Time_Zoned_Offset___hyg_187____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset____x40_Std_Time_Zoned_Offset___hyg_187_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprOffset() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset____x40_Std_Time_Zoned_Offset___hyg_187____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_decEqOffset____x40_Std_Time_Zoned_Offset___hyg_225_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_decEqOffset____x40_Std_Time_Zoned_Offset___hyg_225____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_decEqOffset____x40_Std_Time_Zoned_Offset___hyg_225_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_TimeZone_instDecidableEqOffset(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedOffset() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instOrdOffset() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed), 1, 0);
x_2 = l_Std_Time_Second_instOrdOffset;
x_3 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_2);
lean_closure_set(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_TimeZone_instOrdOffset___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_58; lean_object* x_59; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_nat_to_int(x_99);
x_101 = lean_int_dec_le(x_100, x_1);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_mk_string_unchecked("-", 1, 1);
x_103 = lean_int_neg(x_1);
lean_dec(x_1);
x_58 = x_102;
x_59 = x_103;
goto block_98;
}
else
{
lean_object* x_104; 
x_104 = lean_mk_string_unchecked("+", 1, 1);
x_58 = x_104;
x_59 = x_1;
goto block_98;
}
block_12:
{
if (x_2 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_9 = lean_mk_string_unchecked(":", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
return x_11;
}
}
block_18:
{
lean_object* x_17; 
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_3 = x_13;
x_4 = x_14;
x_5 = x_17;
goto block_12;
}
block_50:
{
if (x_19 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_to_int(x_23);
x_25 = lean_int_dec_lt(x_21, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_nat_abs(x_21);
lean_dec(x_21);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_3 = x_22;
x_4 = x_20;
x_5 = x_27;
goto block_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_nat_abs(x_21);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = lean_mk_string_unchecked("-", 1, 1);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_30, x_32);
lean_dec(x_30);
x_34 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_35 = lean_string_append(x_31, x_34);
lean_dec(x_34);
x_3 = x_22;
x_4 = x_20;
x_5 = x_35;
goto block_12;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_mk_string_unchecked("0", 1, 1);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_int_dec_lt(x_21, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_nat_abs(x_21);
lean_dec(x_21);
x_41 = l___private_Init_Data_Repr_0__Nat_reprFast(x_40);
x_13 = x_22;
x_14 = x_20;
x_15 = x_36;
x_16 = x_41;
goto block_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_nat_abs(x_21);
lean_dec(x_21);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_42, x_43);
lean_dec(x_42);
x_45 = lean_mk_string_unchecked("-", 1, 1);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_44, x_46);
lean_dec(x_44);
x_48 = l___private_Init_Data_Repr_0__Nat_reprFast(x_47);
x_49 = lean_string_append(x_45, x_48);
lean_dec(x_48);
x_13 = x_22;
x_14 = x_20;
x_15 = x_36;
x_16 = x_49;
goto block_18;
}
}
}
block_57:
{
lean_object* x_56; 
x_56 = lean_string_append(x_53, x_55);
lean_dec(x_55);
x_19 = x_52;
x_20 = x_51;
x_21 = x_54;
x_22 = x_56;
goto block_50;
}
block_98:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_60 = lean_unsigned_to_nat(3600u);
x_61 = lean_nat_to_int(x_60);
x_62 = lean_int_ediv(x_59, x_61);
x_63 = lean_int_mod(x_59, x_61);
lean_dec(x_61);
lean_dec(x_59);
x_64 = lean_unsigned_to_nat(60u);
x_65 = lean_nat_to_int(x_64);
x_66 = lean_int_ediv(x_63, x_65);
lean_dec(x_65);
lean_dec(x_63);
x_67 = lean_unsigned_to_nat(10u);
x_68 = lean_nat_to_int(x_67);
x_69 = lean_int_dec_lt(x_62, x_68);
x_70 = lean_int_dec_lt(x_66, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_to_int(x_71);
x_73 = lean_int_dec_lt(x_62, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_nat_abs(x_62);
lean_dec(x_62);
x_75 = l___private_Init_Data_Repr_0__Nat_reprFast(x_74);
x_19 = x_70;
x_20 = x_58;
x_21 = x_66;
x_22 = x_75;
goto block_50;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_nat_abs(x_62);
lean_dec(x_62);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_76, x_77);
lean_dec(x_76);
x_79 = lean_mk_string_unchecked("-", 1, 1);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_78, x_80);
lean_dec(x_78);
x_82 = l___private_Init_Data_Repr_0__Nat_reprFast(x_81);
x_83 = lean_string_append(x_79, x_82);
lean_dec(x_82);
x_19 = x_70;
x_20 = x_58;
x_21 = x_66;
x_22 = x_83;
goto block_50;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_mk_string_unchecked("0", 1, 1);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_to_int(x_85);
x_87 = lean_int_dec_lt(x_62, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_nat_abs(x_62);
lean_dec(x_62);
x_89 = l___private_Init_Data_Repr_0__Nat_reprFast(x_88);
x_51 = x_58;
x_52 = x_70;
x_53 = x_84;
x_54 = x_66;
x_55 = x_89;
goto block_57;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_nat_abs(x_62);
lean_dec(x_62);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_sub(x_90, x_91);
lean_dec(x_90);
x_93 = lean_mk_string_unchecked("-", 1, 1);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_92, x_94);
lean_dec(x_92);
x_96 = l___private_Init_Data_Repr_0__Nat_reprFast(x_95);
x_97 = lean_string_append(x_93, x_96);
lean_dec(x_96);
x_51 = x_58;
x_52 = x_70;
x_53 = x_84;
x_54 = x_66;
x_55 = x_97;
goto block_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Time_TimeZone_Offset_toIsoString(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_zero() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(3600u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_int_mul(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_TimeZone_Offset_ofHours(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(3600u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mul(x_1, x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(60u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_mul(x_2, x_7);
lean_dec(x_7);
x_9 = lean_int_add(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Std_Time_Time(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Offset(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_TimeZone_instReprOffset = _init_l_Std_Time_TimeZone_instReprOffset();
lean_mark_persistent(l_Std_Time_TimeZone_instReprOffset);
l_Std_Time_TimeZone_instInhabitedOffset = _init_l_Std_Time_TimeZone_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedOffset);
l_Std_Time_TimeZone_instOrdOffset = _init_l_Std_Time_TimeZone_instOrdOffset();
lean_mark_persistent(l_Std_Time_TimeZone_instOrdOffset);
l_Std_Time_TimeZone_Offset_zero = _init_l_Std_Time_TimeZone_Offset_zero();
lean_mark_persistent(l_Std_Time_TimeZone_Offset_zero);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
