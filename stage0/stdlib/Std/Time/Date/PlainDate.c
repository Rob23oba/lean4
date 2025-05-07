// Lean compiler output
// Module: Std.Time.Date.PlainDate
// Imports: Std.Time.Internal Std.Time.Date.Basic Std.Internal.Rat
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
lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubOffset__1;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate___redArg____x40_Std_Time_Date_PlainDate___hyg_340____boxed(lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate____x40_Std_Time_Date_PlainDate___hyg_340____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object*);
lean_object* l_Int_repr(lean_object*);
extern lean_object* l_Std_Time_Month_instOrdOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instInhabited;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHAddOffset__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubOffset;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDay_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Year_Offset_weeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedPlainDate;
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate___redArg____x40_Std_Time_Date_PlainDate___hyg_340_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object*, lean_object*);
extern lean_object* l_Std_Time_Day_instOrdOrdinal;
uint8_t l_Std_Time_Day_instDecidableLeOrdinal(lean_object*, lean_object*);
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip___boxed(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate____x40_Std_Time_Date_PlainDate___hyg_340_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object*, uint8_t);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHAddOffset;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_decEqPlainDate____x40_Std_Time_Date_PlainDate___hyg_428____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Time_Date_PlainDate_0__Std_Time_decEqPlainDate____x40_Std_Time_Date_PlainDate___hyg_428_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate___redArg____x40_Std_Time_Date_PlainDate___hyg_340_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("year", 4, 4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_6);
lean_ctor_set(x_64, 1, x_8);
x_65 = lean_unsigned_to_nat(8u);
x_66 = lean_nat_to_int(x_65);
x_96 = lean_ctor_get(x_1, 0);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_to_int(x_97);
x_99 = lean_int_dec_lt(x_96, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Int_repr(x_96);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_67 = x_101;
goto block_95;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = l_Int_repr(x_96);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Repr_addAppParen(x_103, x_97);
x_67 = x_104;
goto block_95;
}
block_36:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_12);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
x_20 = lean_mk_string_unchecked("valid", 5, 5);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
x_24 = lean_mk_string_unchecked("_", 1, 1);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked(" }", 2, 2);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_12);
return x_35;
}
block_63:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_41);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_39);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
lean_inc(x_40);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
x_48 = lean_mk_string_unchecked("day", 3, 3);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_8);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
x_52 = lean_unsigned_to_nat(7u);
x_53 = lean_nat_to_int(x_52);
x_54 = lean_ctor_get(x_1, 2);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_to_int(x_55);
x_57 = lean_int_dec_lt(x_54, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Int_repr(x_54);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_9 = x_39;
x_10 = x_40;
x_11 = x_53;
x_12 = x_41;
x_13 = x_51;
x_14 = x_59;
goto block_36;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = l_Int_repr(x_54);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Repr_addAppParen(x_61, x_55);
x_9 = x_39;
x_10 = x_40;
x_11 = x_53;
x_12 = x_41;
x_13 = x_51;
x_14 = x_62;
goto block_36;
}
}
block_95:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_70, 0, x_68);
x_71 = lean_unbox(x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_71);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_mk_string_unchecked(",", 1, 1);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_inc(x_74);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_box(1);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("month", 5, 5);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_8);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_8);
x_82 = lean_unsigned_to_nat(9u);
x_83 = lean_nat_to_int(x_82);
x_84 = lean_ctor_get(x_1, 1);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_to_int(x_85);
x_87 = lean_int_dec_lt(x_84, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = l_Int_repr(x_84);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_unbox(x_69);
x_37 = x_81;
x_38 = x_83;
x_39 = x_74;
x_40 = x_76;
x_41 = x_90;
x_42 = x_89;
goto block_63;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = l_Int_repr(x_84);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Repr_addAppParen(x_92, x_85);
x_94 = lean_unbox(x_69);
x_37 = x_81;
x_38 = x_83;
x_39 = x_74;
x_40 = x_76;
x_41 = x_94;
x_42 = x_93;
goto block_63;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate____x40_Std_Time_Date_PlainDate___hyg_340_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate___redArg____x40_Std_Time_Date_PlainDate___hyg_340_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate___redArg____x40_Std_Time_Date_PlainDate___hyg_340____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate___redArg____x40_Std_Time_Date_PlainDate___hyg_340_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate____x40_Std_Time_Date_PlainDate___hyg_340____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate____x40_Std_Time_Date_PlainDate___hyg_340_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDate() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Time_Date_PlainDate_0__Std_Time_reprPlainDate____x40_Std_Time_Date_PlainDate___hyg_340____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Date_PlainDate_0__Std_Time_decEqPlainDate____x40_Std_Time_Date_PlainDate___hyg_428_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_int_dec_eq(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_int_dec_eq(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_int_dec_eq(x_5, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_decEqPlainDate____x40_Std_Time_Date_PlainDate___hyg_428____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Time_Date_PlainDate_0__Std_Time_decEqPlainDate____x40_Std_Time_Date_PlainDate___hyg_428_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDate(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Std_Time_Date_PlainDate_0__Std_Time_decEqPlainDate____x40_Std_Time_Date_PlainDate___hyg_428_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_instDecidableEqPlainDate(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
x_3 = lean_unsigned_to_nat(11u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_add(x_2, x_4);
lean_dec(x_4);
x_6 = lean_int_sub(x_5, x_2);
lean_dec(x_5);
x_7 = lean_int_add(x_6, x_2);
lean_dec(x_6);
x_8 = lean_int_sub(x_2, x_2);
x_9 = lean_int_emod(x_8, x_7);
x_10 = lean_int_add(x_9, x_7);
lean_dec(x_9);
x_11 = lean_int_emod(x_10, x_7);
lean_dec(x_7);
lean_dec(x_10);
x_12 = lean_int_add(x_11, x_2);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(30u);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_add(x_2, x_14);
lean_dec(x_14);
x_16 = lean_int_sub(x_15, x_2);
lean_dec(x_15);
x_17 = lean_int_add(x_16, x_2);
lean_dec(x_16);
x_18 = lean_int_emod(x_8, x_17);
lean_dec(x_8);
x_19 = lean_int_add(x_18, x_17);
lean_dec(x_18);
x_20 = lean_int_emod(x_19, x_17);
lean_dec(x_17);
lean_dec(x_19);
x_21 = lean_int_add(x_20, x_2);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDate() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_instOrdPlainDate___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Std_Time_instOrdPlainDate___lam__1___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Std_Time_instOrdPlainDate___lam__2___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_instOrdInt___lam__0___boxed), 2, 0);
x_5 = l_Std_Time_Month_instOrdOrdinal;
x_6 = l_Std_Time_Day_instOrdOrdinal;
x_7 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_1);
x_8 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_2);
x_9 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instOrdPlainDate___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instOrdPlainDate___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instOrdPlainDate___lam__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_mod(x_1, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_dec_eq(x_12, x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_dec(x_14);
x_4 = x_15;
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_unsigned_to_nat(100u);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_mod(x_1, x_17);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_14);
lean_dec(x_18);
x_20 = l_instDecidableNot___redArg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(400u);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_mod(x_1, x_22);
lean_dec(x_22);
x_24 = lean_int_dec_eq(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
x_4 = x_24;
goto block_9;
}
else
{
lean_dec(x_14);
x_4 = x_20;
goto block_9;
}
}
block_9:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Std_Time_Month_Ordinal_days(x_4, x_2);
x_6 = lean_int_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_5);
return x_8;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_unsigned_to_nat(11u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_add(x_4, x_6);
lean_dec(x_6);
x_8 = lean_int_sub(x_7, x_4);
lean_dec(x_7);
x_9 = lean_int_add(x_8, x_4);
lean_dec(x_8);
x_10 = lean_int_sub(x_4, x_4);
x_11 = lean_int_emod(x_10, x_9);
x_12 = lean_int_add(x_11, x_9);
lean_dec(x_11);
x_13 = lean_int_emod(x_12, x_9);
lean_dec(x_9);
lean_dec(x_12);
x_14 = lean_int_add(x_13, x_4);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(30u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_int_add(x_4, x_16);
lean_dec(x_16);
x_18 = lean_int_sub(x_17, x_4);
lean_dec(x_17);
x_19 = lean_int_add(x_18, x_4);
lean_dec(x_18);
x_20 = lean_int_emod(x_10, x_19);
lean_dec(x_10);
x_21 = lean_int_add(x_20, x_19);
lean_dec(x_20);
x_22 = lean_int_emod(x_21, x_19);
lean_dec(x_19);
lean_dec(x_21);
x_23 = lean_int_add(x_22, x_4);
lean_dec(x_4);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDay_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_unsigned_to_nat(4u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_mod(x_1, x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_dec_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_15);
x_4 = x_16;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(100u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_mod(x_1, x_18);
lean_dec(x_18);
x_20 = lean_int_dec_eq(x_19, x_15);
lean_dec(x_19);
x_21 = l_instDecidableNot___redArg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(400u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_mod(x_1, x_23);
lean_dec(x_23);
x_25 = lean_int_dec_eq(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_4 = x_25;
goto block_10;
}
else
{
lean_dec(x_15);
x_4 = x_21;
goto block_10;
}
}
block_10:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Std_Time_Month_Ordinal_days(x_4, x_2);
x_6 = l_Std_Time_Day_instDecidableLeOrdinal(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(4u);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_mod(x_1, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_dec_eq(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_13);
x_3 = x_14;
goto block_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_unsigned_to_nat(100u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_int_mod(x_1, x_16);
lean_dec(x_16);
x_18 = lean_int_dec_eq(x_17, x_13);
lean_dec(x_17);
x_19 = l_instDecidableNot___redArg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_unsigned_to_nat(400u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_mod(x_1, x_21);
lean_dec(x_21);
x_23 = lean_int_dec_eq(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
x_3 = x_23;
goto block_8;
}
else
{
lean_dec(x_13);
x_3 = x_19;
goto block_8;
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Std_Time_ValidDate_ofOrdinal(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_ofYearOrdinal(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_80; uint8_t x_140; 
x_11 = lean_unsigned_to_nat(719468u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_add(x_1, x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_to_int(x_14);
x_140 = lean_int_dec_le(x_15, x_13);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_unsigned_to_nat(146096u);
x_142 = lean_nat_to_int(x_141);
x_143 = lean_int_sub(x_13, x_142);
lean_dec(x_142);
x_80 = x_143;
goto block_139;
}
else
{
lean_inc(x_13);
x_80 = x_13;
goto block_139;
}
block_10:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Std_Time_Month_Ordinal_days(x_5, x_4);
x_7 = lean_int_dec_lt(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_6);
return x_9;
}
}
block_29:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_int_mod(x_16, x_20);
lean_dec(x_20);
x_23 = lean_int_dec_eq(x_22, x_15);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_21;
x_4 = x_19;
x_5 = x_23;
goto block_10;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_int_mod(x_16, x_18);
lean_dec(x_18);
x_25 = lean_int_dec_eq(x_24, x_15);
lean_dec(x_24);
x_26 = l_instDecidableNot___redArg(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_int_mod(x_16, x_17);
lean_dec(x_17);
x_28 = lean_int_dec_eq(x_27, x_15);
lean_dec(x_15);
lean_dec(x_27);
x_2 = x_16;
x_3 = x_21;
x_4 = x_19;
x_5 = x_28;
goto block_10;
}
else
{
lean_dec(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_21;
x_4 = x_19;
x_5 = x_26;
goto block_10;
}
}
}
block_45:
{
uint8_t x_39; 
x_39 = lean_int_dec_le(x_31, x_34);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
x_40 = lean_nat_to_int(x_33);
x_16 = x_30;
x_17 = x_35;
x_18 = x_36;
x_19 = x_38;
x_20 = x_37;
x_21 = x_40;
goto block_29;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_33);
x_41 = lean_unsigned_to_nat(31u);
x_42 = lean_nat_to_int(x_41);
x_43 = lean_int_dec_le(x_34, x_42);
lean_dec(x_34);
if (x_43 == 0)
{
lean_dec(x_32);
lean_dec(x_31);
x_16 = x_30;
x_17 = x_35;
x_18 = x_36;
x_19 = x_38;
x_20 = x_37;
x_21 = x_42;
goto block_29;
}
else
{
lean_object* x_44; 
lean_dec(x_42);
x_44 = lean_int_add(x_32, x_31);
lean_dec(x_31);
lean_dec(x_32);
x_16 = x_30;
x_17 = x_35;
x_18 = x_36;
x_19 = x_38;
x_20 = x_37;
x_21 = x_44;
goto block_29;
}
}
}
block_65:
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_int_add(x_48, x_57);
lean_dec(x_57);
lean_dec(x_48);
x_59 = lean_int_dec_le(x_47, x_49);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_49);
lean_dec(x_46);
lean_inc(x_50);
x_60 = lean_nat_to_int(x_50);
x_30 = x_58;
x_31 = x_47;
x_32 = x_51;
x_33 = x_50;
x_34 = x_53;
x_35 = x_52;
x_36 = x_55;
x_37 = x_56;
x_38 = x_60;
goto block_45;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_unsigned_to_nat(12u);
x_62 = lean_nat_to_int(x_61);
x_63 = lean_int_dec_le(x_49, x_62);
lean_dec(x_49);
if (x_63 == 0)
{
lean_dec(x_54);
lean_dec(x_46);
x_30 = x_58;
x_31 = x_47;
x_32 = x_51;
x_33 = x_50;
x_34 = x_53;
x_35 = x_52;
x_36 = x_55;
x_37 = x_56;
x_38 = x_62;
goto block_45;
}
else
{
lean_object* x_64; 
lean_dec(x_62);
x_64 = lean_int_add(x_46, x_54);
lean_dec(x_54);
lean_dec(x_46);
x_30 = x_58;
x_31 = x_47;
x_32 = x_51;
x_33 = x_50;
x_34 = x_53;
x_35 = x_52;
x_36 = x_55;
x_37 = x_56;
x_38 = x_64;
goto block_45;
}
}
}
block_79:
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_int_add(x_66, x_76);
x_78 = lean_int_dec_le(x_77, x_67);
lean_dec(x_67);
if (x_78 == 0)
{
lean_inc(x_15);
x_46 = x_66;
x_47 = x_68;
x_48 = x_69;
x_49 = x_77;
x_50 = x_71;
x_51 = x_70;
x_52 = x_73;
x_53 = x_72;
x_54 = x_76;
x_55 = x_74;
x_56 = x_75;
x_57 = x_15;
goto block_65;
}
else
{
lean_inc(x_68);
x_46 = x_66;
x_47 = x_68;
x_48 = x_69;
x_49 = x_77;
x_50 = x_71;
x_51 = x_70;
x_52 = x_73;
x_53 = x_72;
x_54 = x_76;
x_55 = x_74;
x_56 = x_75;
x_57 = x_68;
goto block_65;
}
}
block_139:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_81 = lean_unsigned_to_nat(146097u);
x_82 = lean_nat_to_int(x_81);
x_83 = lean_int_div(x_80, x_82);
lean_dec(x_80);
x_84 = lean_int_mul(x_83, x_82);
lean_dec(x_82);
x_85 = lean_int_sub(x_13, x_84);
lean_dec(x_84);
lean_dec(x_13);
x_86 = lean_unsigned_to_nat(1460u);
x_87 = lean_nat_to_int(x_86);
x_88 = lean_int_div(x_85, x_87);
lean_dec(x_87);
x_89 = lean_int_sub(x_85, x_88);
lean_dec(x_88);
x_90 = lean_unsigned_to_nat(36524u);
x_91 = lean_nat_to_int(x_90);
x_92 = lean_int_div(x_85, x_91);
lean_dec(x_91);
x_93 = lean_int_add(x_89, x_92);
lean_dec(x_92);
lean_dec(x_89);
x_94 = lean_unsigned_to_nat(146096u);
x_95 = lean_nat_to_int(x_94);
x_96 = lean_int_div(x_85, x_95);
lean_dec(x_95);
x_97 = lean_int_sub(x_93, x_96);
lean_dec(x_96);
lean_dec(x_93);
x_98 = lean_unsigned_to_nat(365u);
x_99 = lean_nat_to_int(x_98);
x_100 = lean_int_div(x_97, x_99);
lean_dec(x_97);
x_101 = lean_unsigned_to_nat(400u);
x_102 = lean_nat_to_int(x_101);
x_103 = lean_int_mul(x_83, x_102);
lean_dec(x_83);
x_104 = lean_int_add(x_100, x_103);
lean_dec(x_103);
x_105 = lean_int_mul(x_99, x_100);
lean_dec(x_99);
x_106 = lean_unsigned_to_nat(4u);
x_107 = lean_nat_to_int(x_106);
x_108 = lean_int_div(x_100, x_107);
x_109 = lean_int_add(x_105, x_108);
lean_dec(x_108);
lean_dec(x_105);
x_110 = lean_unsigned_to_nat(100u);
x_111 = lean_nat_to_int(x_110);
x_112 = lean_int_div(x_100, x_111);
lean_dec(x_100);
x_113 = lean_int_sub(x_109, x_112);
lean_dec(x_112);
lean_dec(x_109);
x_114 = lean_int_sub(x_85, x_113);
lean_dec(x_113);
lean_dec(x_85);
x_115 = lean_unsigned_to_nat(5u);
x_116 = lean_nat_to_int(x_115);
x_117 = lean_int_mul(x_116, x_114);
x_118 = lean_unsigned_to_nat(2u);
x_119 = lean_nat_to_int(x_118);
x_120 = lean_int_add(x_117, x_119);
lean_dec(x_117);
x_121 = lean_unsigned_to_nat(153u);
x_122 = lean_nat_to_int(x_121);
x_123 = lean_int_div(x_120, x_122);
lean_dec(x_120);
x_124 = lean_int_mul(x_122, x_123);
lean_dec(x_122);
x_125 = lean_int_add(x_124, x_119);
lean_dec(x_124);
x_126 = lean_int_div(x_125, x_116);
lean_dec(x_116);
lean_dec(x_125);
x_127 = lean_int_sub(x_114, x_126);
lean_dec(x_126);
lean_dec(x_114);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_to_int(x_128);
x_130 = lean_int_add(x_127, x_129);
x_131 = lean_unsigned_to_nat(10u);
x_132 = lean_nat_to_int(x_131);
x_133 = lean_int_dec_lt(x_123, x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_unsigned_to_nat(9u);
x_135 = lean_nat_to_int(x_134);
x_136 = lean_int_neg(x_135);
lean_dec(x_135);
x_66 = x_123;
x_67 = x_119;
x_68 = x_129;
x_69 = x_104;
x_70 = x_127;
x_71 = x_128;
x_72 = x_130;
x_73 = x_102;
x_74 = x_111;
x_75 = x_107;
x_76 = x_136;
goto block_79;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_unsigned_to_nat(3u);
x_138 = lean_nat_to_int(x_137);
x_66 = x_123;
x_67 = x_119;
x_68 = x_129;
x_69 = x_104;
x_70 = x_127;
x_71 = x_128;
x_72 = x_130;
x_73 = x_102;
x_74 = x_111;
x_75 = x_107;
x_76 = x_138;
goto block_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_unsigned_to_nat(7u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_int_neg(x_3);
x_8 = lean_int_add(x_6, x_7);
lean_dec(x_7);
x_9 = lean_int_ediv(x_8, x_5);
lean_dec(x_5);
lean_dec(x_8);
x_10 = lean_int_add(x_9, x_3);
lean_dec(x_3);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDate_weekOfMonth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_unsigned_to_nat(3u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_int_neg(x_3);
x_8 = lean_int_add(x_6, x_7);
lean_dec(x_7);
x_9 = lean_int_ediv(x_8, x_5);
lean_dec(x_5);
lean_dec(x_8);
x_10 = lean_int_add(x_9, x_3);
lean_dec(x_3);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDate_quarter(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_unsigned_to_nat(4u);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_mod(x_8, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_dec_eq(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_13);
x_2 = x_14;
goto block_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_unsigned_to_nat(100u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_int_mod(x_8, x_16);
lean_dec(x_16);
x_18 = lean_int_dec_eq(x_17, x_13);
lean_dec(x_17);
x_19 = l_instDecidableNot___redArg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_unsigned_to_nat(400u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_mod(x_8, x_21);
lean_dec(x_21);
x_23 = lean_int_dec_eq(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
x_2 = x_23;
goto block_7;
}
else
{
lean_dec(x_13);
x_2 = x_19;
goto block_7;
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Std_Time_ValidDate_dayOfYear(x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDate_dayOfYear(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_Time_Year_Offset_era(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_PlainDate_era(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mod(x_2, x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_dec_eq(x_5, x_7);
lean_dec(x_5);
if (x_8 == 0)
{
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(100u);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_mod(x_2, x_10);
lean_dec(x_10);
x_12 = lean_int_dec_eq(x_11, x_7);
lean_dec(x_11);
x_13 = l_instDecidableNot___redArg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(400u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_mod(x_2, x_15);
lean_dec(x_15);
x_17 = lean_int_dec_eq(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
return x_17;
}
else
{
lean_dec(x_7);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_PlainDate_inLeapYear(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_40; lean_object* x_41; lean_object* x_57; uint8_t x_65; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_65 = lean_int_dec_lt(x_3, x_6);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_int_sub(x_66, x_5);
lean_dec(x_66);
x_57 = x_67;
goto block_64;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_57 = x_68;
goto block_64;
}
block_39:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_12 = lean_int_add(x_6, x_11);
lean_dec(x_11);
lean_dec(x_6);
x_13 = lean_int_mul(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = lean_int_add(x_13, x_3);
lean_dec(x_3);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_int_div(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = lean_int_add(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
x_19 = lean_int_sub(x_18, x_5);
lean_dec(x_5);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(365u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_mul(x_8, x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(4u);
x_24 = lean_nat_to_int(x_23);
x_25 = lean_int_div(x_8, x_24);
lean_dec(x_24);
x_26 = lean_int_add(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_27 = lean_unsigned_to_nat(100u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_div(x_8, x_28);
lean_dec(x_28);
lean_dec(x_8);
x_30 = lean_int_sub(x_26, x_29);
lean_dec(x_29);
lean_dec(x_26);
x_31 = lean_int_add(x_30, x_19);
lean_dec(x_19);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(146097u);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_int_mul(x_9, x_33);
lean_dec(x_33);
lean_dec(x_9);
x_35 = lean_int_add(x_34, x_31);
lean_dec(x_31);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(719468u);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_int_sub(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
return x_38;
}
block_56:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_unsigned_to_nat(400u);
x_43 = lean_nat_to_int(x_42);
x_44 = lean_int_div(x_41, x_43);
lean_dec(x_41);
x_45 = lean_int_mul(x_44, x_43);
lean_dec(x_43);
x_46 = lean_int_sub(x_40, x_45);
lean_dec(x_45);
lean_dec(x_40);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_unsigned_to_nat(153u);
x_49 = lean_nat_to_int(x_48);
x_50 = lean_int_dec_lt(x_3, x_6);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_unsigned_to_nat(9u);
x_52 = lean_nat_to_int(x_51);
x_7 = x_47;
x_8 = x_46;
x_9 = x_44;
x_10 = x_49;
x_11 = x_52;
goto block_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_int_neg(x_54);
lean_dec(x_54);
x_7 = x_47;
x_8 = x_46;
x_9 = x_44;
x_10 = x_49;
x_11 = x_55;
goto block_39;
}
}
block_64:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_to_int(x_58);
x_60 = lean_int_dec_le(x_59, x_57);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_unsigned_to_nat(399u);
x_62 = lean_nat_to_int(x_61);
x_63 = lean_int_sub(x_57, x_62);
lean_dec(x_62);
x_40 = x_57;
x_41 = x_63;
goto block_56;
}
else
{
lean_inc(x_57);
x_40 = x_57;
x_41 = x_57;
goto block_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_4 = lean_int_add(x_3, x_2);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_addDays(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_int_neg(x_2);
x_4 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_5 = lean_int_add(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_subDays(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(7u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_7 = lean_int_add(x_6, x_5);
lean_dec(x_5);
lean_dec(x_6);
x_8 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_addWeeks(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_int_neg(x_2);
x_4 = lean_unsigned_to_nat(7u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_mul(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
x_7 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_8 = lean_int_add(x_7, x_6);
lean_dec(x_6);
lean_dec(x_7);
x_9 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_subWeeks(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_sub(x_3, x_5);
x_7 = lean_int_add(x_6, x_2);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(12u);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_int_emod(x_7, x_9);
x_11 = lean_int_add(x_10, x_5);
lean_dec(x_5);
lean_dec(x_10);
x_12 = lean_int_ediv(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 2);
x_22 = lean_unsigned_to_nat(4u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_mod(x_14, x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_dec_eq(x_24, x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_dec(x_26);
x_16 = x_27;
goto block_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_28 = lean_unsigned_to_nat(100u);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_int_mod(x_14, x_29);
lean_dec(x_29);
x_31 = lean_int_dec_eq(x_30, x_26);
lean_dec(x_30);
x_32 = l_instDecidableNot___redArg(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_unsigned_to_nat(400u);
x_34 = lean_nat_to_int(x_33);
x_35 = lean_int_mod(x_14, x_34);
lean_dec(x_34);
x_36 = lean_int_dec_eq(x_35, x_26);
lean_dec(x_26);
lean_dec(x_35);
x_16 = x_36;
goto block_21;
}
else
{
lean_dec(x_26);
x_16 = x_32;
goto block_21;
}
}
block_21:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_Time_Month_Ordinal_days(x_16, x_11);
x_18 = lean_int_dec_lt(x_17, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_inc(x_15);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_15);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_17);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_addMonthsClip(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_int_neg(x_2);
x_4 = l_Std_Time_PlainDate_addMonthsClip(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_subMonthsClip(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_4 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_to_int(x_4);
x_13 = lean_unsigned_to_nat(30u);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_add(x_12, x_14);
lean_dec(x_14);
x_16 = lean_int_sub(x_15, x_12);
lean_dec(x_15);
x_17 = lean_int_add(x_16, x_12);
lean_dec(x_16);
x_18 = lean_int_sub(x_12, x_12);
x_19 = lean_int_emod(x_18, x_17);
lean_dec(x_18);
x_20 = lean_int_add(x_19, x_17);
lean_dec(x_19);
x_21 = lean_int_emod(x_20, x_17);
lean_dec(x_17);
lean_dec(x_20);
x_22 = lean_int_add(x_21, x_12);
lean_dec(x_12);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_int_mod(x_1, x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_int_dec_eq(x_31, x_33);
lean_dec(x_31);
if (x_34 == 0)
{
lean_dec(x_33);
x_23 = x_34;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_35 = lean_unsigned_to_nat(100u);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_int_mod(x_1, x_36);
lean_dec(x_36);
x_38 = lean_int_dec_eq(x_37, x_33);
lean_dec(x_37);
x_39 = l_instDecidableNot___redArg(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_unsigned_to_nat(400u);
x_41 = lean_nat_to_int(x_40);
x_42 = lean_int_mod(x_1, x_41);
lean_dec(x_41);
x_43 = lean_int_dec_eq(x_42, x_33);
lean_dec(x_33);
lean_dec(x_42);
x_23 = x_43;
goto block_28;
}
else
{
lean_dec(x_33);
x_23 = x_39;
goto block_28;
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_nat_to_int(x_4);
x_7 = lean_int_sub(x_3, x_6);
lean_dec(x_6);
x_8 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_5);
x_9 = lean_int_add(x_8, x_7);
lean_dec(x_7);
lean_dec(x_8);
x_10 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_9);
lean_dec(x_9);
return x_10;
}
block_28:
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Std_Time_Month_Ordinal_days(x_23, x_2);
x_25 = lean_int_dec_lt(x_24, x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_22);
x_5 = x_26;
goto block_11;
}
else
{
lean_object* x_27; 
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_24);
x_5 = x_27;
goto block_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_PlainDate_rollOver(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_11 = lean_unsigned_to_nat(4u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_mod(x_2, x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_dec_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_15);
x_5 = x_16;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(100u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_mod(x_2, x_18);
lean_dec(x_18);
x_20 = lean_int_dec_eq(x_19, x_15);
lean_dec(x_19);
x_21 = l_instDecidableNot___redArg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(400u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_mod(x_2, x_23);
lean_dec(x_23);
x_25 = lean_int_dec_eq(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_5 = x_25;
goto block_10;
}
else
{
lean_dec(x_15);
x_5 = x_21;
goto block_10;
}
}
block_10:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Std_Time_Month_Ordinal_days(x_5, x_3);
x_7 = lean_int_dec_lt(x_6, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_6);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_withYearClip(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_Time_PlainDate_rollOver(x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_to_int(x_5);
x_16 = lean_unsigned_to_nat(30u);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_add(x_15, x_17);
lean_dec(x_17);
x_19 = lean_int_sub(x_18, x_15);
lean_dec(x_18);
x_20 = lean_int_add(x_19, x_15);
lean_dec(x_19);
x_21 = lean_int_sub(x_15, x_15);
x_22 = lean_int_emod(x_21, x_20);
lean_dec(x_21);
x_23 = lean_int_add(x_22, x_20);
lean_dec(x_22);
x_24 = lean_int_emod(x_23, x_20);
lean_dec(x_20);
lean_dec(x_23);
x_25 = lean_int_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_nat_to_int(x_32);
x_34 = lean_int_mod(x_3, x_33);
lean_dec(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_int_dec_eq(x_34, x_36);
lean_dec(x_34);
if (x_37 == 0)
{
lean_dec(x_36);
x_26 = x_37;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_38 = lean_unsigned_to_nat(100u);
x_39 = lean_nat_to_int(x_38);
x_40 = lean_int_mod(x_3, x_39);
lean_dec(x_39);
x_41 = lean_int_dec_eq(x_40, x_36);
lean_dec(x_40);
x_42 = l_instDecidableNot___redArg(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_unsigned_to_nat(400u);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_int_mod(x_3, x_44);
lean_dec(x_44);
x_46 = lean_int_dec_eq(x_45, x_36);
lean_dec(x_36);
lean_dec(x_45);
x_26 = x_46;
goto block_31;
}
else
{
lean_dec(x_36);
x_26 = x_42;
goto block_31;
}
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Std_Time_PlainDate_addMonthsClip(x_6, x_2);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_nat_to_int(x_5);
x_10 = lean_int_sub(x_8, x_9);
lean_dec(x_9);
x_11 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_7);
x_12 = lean_int_add(x_11, x_10);
lean_dec(x_10);
lean_dec(x_11);
x_13 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_12);
lean_dec(x_12);
return x_13;
}
block_31:
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Std_Time_Month_Ordinal_days(x_26, x_4);
x_28 = lean_int_dec_lt(x_27, x_25);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_inc(x_4);
lean_inc(x_3);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 2, x_25);
x_6 = x_29;
goto block_14;
}
else
{
lean_object* x_30; 
lean_dec(x_25);
lean_inc(x_4);
lean_inc(x_3);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_27);
x_6 = x_30;
goto block_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_addMonthsRollOver(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_int_neg(x_2);
x_4 = l_Std_Time_PlainDate_addMonthsRollOver(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_subMonthsRollOver(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(12u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_addMonthsRollOver(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_addYearsRollOver(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(12u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
x_6 = lean_int_neg(x_5);
lean_dec(x_5);
x_7 = l_Std_Time_PlainDate_addMonthsRollOver(x_1, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_subYearsRollOver(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(12u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_addMonthsClip(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_addYearsClip(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(12u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
x_6 = lean_int_neg(x_5);
lean_dec(x_5);
x_7 = l_Std_Time_PlainDate_addMonthsClip(x_1, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_subYearsClip(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_11 = lean_unsigned_to_nat(4u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_mod(x_3, x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_dec_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_15);
x_5 = x_16;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(100u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_mod(x_3, x_18);
lean_dec(x_18);
x_20 = lean_int_dec_eq(x_19, x_15);
lean_dec(x_19);
x_21 = l_instDecidableNot___redArg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(400u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_mod(x_3, x_23);
lean_dec(x_23);
x_25 = lean_int_dec_eq(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_5 = x_25;
goto block_10;
}
else
{
lean_dec(x_15);
x_5 = x_21;
goto block_10;
}
}
block_10:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Std_Time_Month_Ordinal_days(x_5, x_4);
x_7 = lean_int_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_2);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_6);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_withDaysClip(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_Time_PlainDate_rollOver(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_withDaysRollOver(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_11 = lean_unsigned_to_nat(4u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_mod(x_3, x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_dec_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_15);
x_5 = x_16;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(100u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_mod(x_3, x_18);
lean_dec(x_18);
x_20 = lean_int_dec_eq(x_19, x_15);
lean_dec(x_19);
x_21 = l_instDecidableNot___redArg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(400u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_mod(x_3, x_23);
lean_dec(x_23);
x_25 = lean_int_dec_eq(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_5 = x_25;
goto block_10;
}
else
{
lean_dec(x_15);
x_5 = x_21;
goto block_10;
}
}
block_10:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Std_Time_Month_Ordinal_days(x_5, x_2);
x_7 = lean_int_dec_lt(x_6, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_6);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_withMonthClip(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_Time_PlainDate_rollOver(x_3, x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_weekday(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_17 = lean_unsigned_to_nat(4u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_neg(x_18);
x_20 = lean_int_dec_le(x_19, x_16);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(5u);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_add(x_16, x_22);
lean_dec(x_22);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(7u);
x_25 = lean_nat_to_int(x_24);
x_26 = lean_int_emod(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
x_27 = lean_unsigned_to_nat(6u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_2 = x_29;
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_int_add(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
x_31 = lean_unsigned_to_nat(7u);
x_32 = lean_nat_to_int(x_31);
x_33 = lean_int_emod(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
x_2 = x_33;
goto block_15;
}
block_15:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_unsigned_to_nat(7u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_sub(x_6, x_4);
lean_dec(x_6);
x_8 = lean_int_add(x_7, x_4);
lean_dec(x_7);
x_9 = lean_int_sub(x_2, x_4);
lean_dec(x_2);
x_10 = lean_int_emod(x_9, x_8);
lean_dec(x_9);
x_11 = lean_int_add(x_10, x_8);
lean_dec(x_10);
x_12 = lean_int_emod(x_11, x_8);
lean_dec(x_8);
lean_dec(x_11);
x_13 = lean_int_add(x_12, x_4);
lean_dec(x_4);
lean_dec(x_12);
x_14 = l_Std_Time_Weekday_ofOrdinal(x_13);
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_PlainDate_weekday(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_unsigned_to_nat(7u);
x_5 = lean_nat_to_int(x_4);
x_17 = lean_unsigned_to_nat(30u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_add(x_3, x_18);
lean_dec(x_18);
x_20 = lean_int_sub(x_19, x_3);
lean_dec(x_19);
x_21 = lean_int_add(x_20, x_3);
lean_dec(x_20);
x_22 = lean_int_sub(x_3, x_3);
x_23 = lean_int_emod(x_22, x_21);
lean_dec(x_22);
x_24 = lean_int_add(x_23, x_21);
lean_dec(x_23);
x_25 = lean_int_emod(x_24, x_21);
lean_dec(x_21);
lean_dec(x_24);
x_26 = lean_int_add(x_25, x_3);
lean_dec(x_25);
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_int_mod(x_27, x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_to_int(x_38);
x_40 = lean_int_dec_eq(x_37, x_39);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_39);
x_29 = x_40;
goto block_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; 
x_41 = lean_unsigned_to_nat(100u);
x_42 = lean_nat_to_int(x_41);
x_43 = lean_int_mod(x_27, x_42);
lean_dec(x_42);
x_44 = lean_int_dec_eq(x_43, x_39);
lean_dec(x_43);
x_45 = l_instDecidableNot___redArg(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_unsigned_to_nat(400u);
x_47 = lean_nat_to_int(x_46);
x_48 = lean_int_mod(x_27, x_47);
lean_dec(x_47);
x_49 = lean_int_dec_eq(x_48, x_39);
lean_dec(x_39);
lean_dec(x_48);
x_29 = x_49;
goto block_34;
}
else
{
lean_dec(x_39);
x_29 = x_45;
goto block_34;
}
}
block_16:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Std_Time_PlainDate_weekday(x_6);
x_8 = lean_int_neg(x_3);
x_9 = l_Std_Time_Weekday_toOrdinal(x_7);
x_10 = lean_int_add(x_9, x_8);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_int_add(x_11, x_8);
lean_dec(x_8);
x_13 = lean_int_add(x_12, x_10);
lean_dec(x_10);
lean_dec(x_12);
x_14 = lean_int_ediv(x_13, x_5);
lean_dec(x_5);
lean_dec(x_13);
x_15 = lean_int_add(x_14, x_3);
lean_dec(x_3);
lean_dec(x_14);
return x_15;
}
block_34:
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Std_Time_Month_Ordinal_days(x_29, x_28);
x_31 = lean_int_dec_lt(x_30, x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_inc(x_28);
lean_inc(x_27);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_26);
x_6 = x_32;
goto block_16;
}
else
{
lean_object* x_33; 
lean_dec(x_26);
lean_inc(x_28);
lean_inc(x_27);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_30);
x_6 = x_33;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDate_alignedWeekOfMonth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_8 = l_Std_Time_PlainDate_weekday(x_1);
x_9 = l_Std_Time_Weekday_toOrdinal(x_8);
x_10 = lean_int_neg(x_9);
lean_dec(x_9);
x_11 = l_Std_Time_Weekday_toOrdinal(x_2);
x_12 = lean_int_add(x_11, x_10);
lean_dec(x_10);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_dec_lt(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
x_3 = x_12;
goto block_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_add(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_3 = x_18;
goto block_7;
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_5 = lean_int_add(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Std_Time_PlainDate_withWeekday(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(10u);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_unsigned_to_nat(7u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_nat_to_int(x_3);
x_9 = l_Std_Time_PlainDate_dayOfYear(x_1);
x_10 = lean_int_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Std_Time_PlainDate_weekday(x_1);
x_12 = l_Std_Time_Weekday_toOrdinal(x_11);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
x_14 = lean_int_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = lean_int_ediv(x_14, x_7);
lean_dec(x_7);
lean_dec(x_14);
x_16 = lean_int_dec_lt(x_15, x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_Time_Year_Offset_weeks(x_2);
lean_dec(x_2);
x_18 = lean_int_dec_lt(x_17, x_15);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_5);
return x_15;
}
else
{
lean_dec(x_15);
return x_5;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = lean_int_sub(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_20 = l_Std_Time_Year_Offset_weeks(x_19);
lean_dec(x_19);
return x_20;
}
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHAddOffset() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_PlainDate_addDays___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubOffset() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_PlainDate_subDays___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHAddOffset__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_PlainDate_addWeeks___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubOffset__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_PlainDate_subWeeks___boxed), 2, 0);
return x_1;
}
}
lean_object* initialize_Std_Time_Internal(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Rat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_PlainDate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Rat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instReprPlainDate = _init_l_Std_Time_instReprPlainDate();
lean_mark_persistent(l_Std_Time_instReprPlainDate);
l_Std_Time_instInhabitedPlainDate = _init_l_Std_Time_instInhabitedPlainDate();
lean_mark_persistent(l_Std_Time_instInhabitedPlainDate);
l_Std_Time_instOrdPlainDate = _init_l_Std_Time_instOrdPlainDate();
lean_mark_persistent(l_Std_Time_instOrdPlainDate);
l_Std_Time_PlainDate_instInhabited = _init_l_Std_Time_PlainDate_instInhabited();
lean_mark_persistent(l_Std_Time_PlainDate_instInhabited);
l_Std_Time_PlainDate_instHAddOffset = _init_l_Std_Time_PlainDate_instHAddOffset();
lean_mark_persistent(l_Std_Time_PlainDate_instHAddOffset);
l_Std_Time_PlainDate_instHSubOffset = _init_l_Std_Time_PlainDate_instHSubOffset();
lean_mark_persistent(l_Std_Time_PlainDate_instHSubOffset);
l_Std_Time_PlainDate_instHAddOffset__1 = _init_l_Std_Time_PlainDate_instHAddOffset__1();
lean_mark_persistent(l_Std_Time_PlainDate_instHAddOffset__1);
l_Std_Time_PlainDate_instHSubOffset__1 = _init_l_Std_Time_PlainDate_instHSubOffset__1();
lean_mark_persistent(l_Std_Time_PlainDate_instHSubOffset__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
