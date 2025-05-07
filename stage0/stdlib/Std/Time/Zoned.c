// Lean compiler output
// Module: Std.Time.Zoned
// Imports: Std.Time.Zoned.DateTime Std.Time.Zoned.ZoneRules Std.Time.Zoned.ZonedDateTime Std.Time.Zoned.Database
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now(lean_object*);
lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* l_Array_findFinIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Time_PlainTime_midnight;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate___boxed(lean_object*);
lean_object* l_Array_back_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_get_current_time(lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDate___lam__1(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime___boxed(lean_object*);
lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_now(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_current_time(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_Time_Database_defaultGetLocalZoneRules(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_31; lean_object* x_32; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_inc(x_3);
x_32 = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(x_31, x_3);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_6, 0);
lean_inc(x_33);
lean_dec(x_6);
x_9 = x_33;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_9 = x_35;
goto block_30;
}
block_30:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
lean_dec(x_3);
x_11 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_9);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1000000000u);
x_13 = lean_nat_to_int(x_12);
x_14 = l_Std_Time_TimeZone_toSeconds(x_11);
lean_dec(x_11);
x_15 = lean_int_mul(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_10);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_15);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_int_mul(x_18, x_13);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_int_add(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_int_mul(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_int_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_int_add(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
x_27 = l_Std_Time_Duration_ofNanoseconds(x_26);
lean_dec(x_26);
x_28 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_8)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_8;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
else
{
uint8_t x_36; 
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
return x_5;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_5);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
return x_2;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_2);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_now(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_current_time(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_Time_Database_defaultGetLocalZoneRules(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_32; lean_object* x_33; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_3);
x_33 = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(x_32, x_3);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
lean_dec(x_6);
x_9 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_9 = x_36;
goto block_31;
}
block_31:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
lean_dec(x_3);
x_11 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_9);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1000000000u);
x_13 = lean_nat_to_int(x_12);
x_14 = l_Std_Time_TimeZone_toSeconds(x_11);
lean_dec(x_11);
x_15 = lean_int_mul(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_10);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_15);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_int_mul(x_18, x_13);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_int_add(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_int_mul(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_int_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_int_add(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
x_27 = l_Std_Time_Duration_ofNanoseconds(x_26);
lean_dec(x_26);
x_28 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_is_scalar(x_8)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_8;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
else
{
uint8_t x_37; 
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_5, 0);
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_5);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_now(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_current_time(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_Time_Database_defaultGetLocalZoneRules(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_32; lean_object* x_33; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_3);
x_33 = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(x_32, x_3);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
lean_dec(x_6);
x_9 = x_34;
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_9 = x_36;
goto block_31;
}
block_31:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
lean_dec(x_3);
x_11 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_9);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1000000000u);
x_13 = lean_nat_to_int(x_12);
x_14 = l_Std_Time_TimeZone_toSeconds(x_11);
lean_dec(x_11);
x_15 = lean_int_mul(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_10);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_15);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_int_mul(x_18, x_13);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_int_add(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_int_mul(x_22, x_13);
lean_dec(x_13);
lean_dec(x_22);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_int_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_int_add(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
x_27 = l_Std_Time_Duration_ofNanoseconds(x_26);
lean_dec(x_26);
x_28 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
if (lean_is_scalar(x_8)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_8;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
else
{
uint8_t x_37; 
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_5, 0);
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_5);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_5 = lean_unsigned_to_nat(1000000000u);
x_6 = lean_nat_to_int(x_5);
x_7 = l_Std_Time_TimeZone_toSeconds(x_2);
x_8 = lean_int_mul(x_7, x_6);
lean_dec(x_7);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_10 = l_Std_Time_Duration_ofNanoseconds(x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_int_mul(x_11, x_6);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_int_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_int_mul(x_15, x_6);
lean_dec(x_6);
lean_dec(x_15);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_int_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_int_add(x_14, x_18);
lean_dec(x_18);
lean_dec(x_14);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_unsigned_to_nat(86400u);
x_4 = lean_nat_to_int(x_3);
x_5 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_6 = lean_int_mul(x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDate___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_mk_thunk(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofPlainDate___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(86400u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_ediv(x_3, x_5);
lean_dec(x_5);
x_7 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_unsigned_to_nat(86400u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_ediv(x_4, x_6);
lean_dec(x_6);
x_8 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toPlainDate___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_toPlainDate(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toPlainTime___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_toPlainTime(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_5 = lean_unsigned_to_nat(1000000000u);
x_6 = lean_nat_to_int(x_5);
x_7 = l_Std_Time_TimeZone_toSeconds(x_2);
x_8 = lean_int_mul(x_7, x_6);
lean_dec(x_7);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_10 = l_Std_Time_Duration_ofNanoseconds(x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_int_mul(x_11, x_6);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_int_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_int_mul(x_15, x_6);
lean_dec(x_6);
lean_dec(x_15);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_int_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_int_add(x_14, x_18);
lean_dec(x_18);
lean_dec(x_14);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_current_time(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_mk_thunk(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Std_Time_DateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_mk_thunk(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_now___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_now___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_5 = lean_unsigned_to_nat(1000000000u);
x_6 = lean_nat_to_int(x_5);
x_7 = l_Std_Time_TimeZone_toSeconds(x_2);
x_8 = lean_int_mul(x_7, x_6);
lean_dec(x_7);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_10 = l_Std_Time_Duration_ofNanoseconds(x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_int_mul(x_11, x_6);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_int_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_int_mul(x_15, x_6);
lean_dec(x_6);
lean_dec(x_15);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_int_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_int_add(x_14, x_18);
lean_dec(x_18);
lean_dec(x_14);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_current_time(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_Time_Database_defaultGetLocalZoneRules(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_3);
x_16 = l_Std_Time_TimeZone_Transition_timezoneAt(x_15, x_3);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
lean_dec(x_17);
x_9 = x_18;
goto block_14;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_9 = x_19;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_9);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_mk_thunk(x_10);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_9);
if (lean_is_scalar(x_8)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_8;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_now___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_ZonedDateTime_now___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nowAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_current_time(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Std_Time_Database_defaultGetZoneRules(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_4);
x_17 = l_Std_Time_TimeZone_Transition_timezoneAt(x_16, x_4);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_18);
lean_dec(x_18);
x_10 = x_19;
goto block_15;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_10 = x_20;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_10);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_now___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_mk_thunk(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_7);
lean_ctor_set(x_13, 3, x_10);
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_9;
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
return x_3;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_6 = lean_int_mul(x_2, x_3);
x_7 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_5);
x_8 = l_Std_Time_Duration_ofNanoseconds(x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_int_mul(x_9, x_3);
lean_dec(x_9);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_int_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_int_mul(x_13, x_3);
lean_dec(x_13);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_int_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_int_add(x_12, x_16);
lean_dec(x_16);
lean_dec(x_12);
x_18 = l_Std_Time_Duration_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDate___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_int_dec_le(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_27; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_3 = l_Std_Time_PlainTime_midnight;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_inc(x_4);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_findFinIdx_x3f_loop___redArg(x_32, x_33, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_31);
x_36 = l_Array_back_x3f(lean_box(0), x_33);
lean_dec(x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_5 = x_37;
goto block_26;
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_27 = x_38;
goto block_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_39, x_40);
x_42 = lean_array_fget(x_33, x_41);
lean_dec(x_41);
x_43 = lean_array_fget(x_33, x_39);
lean_dec(x_39);
lean_dec(x_33);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_nat_abs(x_46);
lean_dec(x_46);
x_48 = lean_nat_to_int(x_47);
x_49 = lean_int_sub(x_44, x_48);
lean_dec(x_48);
lean_dec(x_44);
x_50 = lean_int_dec_lt(x_31, x_49);
lean_dec(x_49);
lean_dec(x_31);
if (x_50 == 0)
{
lean_dec(x_42);
x_27 = x_43;
goto block_29;
}
else
{
lean_dec(x_43);
x_27 = x_42;
goto block_29;
}
}
block_26:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_5);
lean_dec(x_5);
x_7 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_to_int(x_8);
x_10 = l_Std_Time_TimeZone_toSeconds(x_6);
x_11 = lean_int_neg(x_10);
x_12 = lean_int_neg(x_9);
lean_dec(x_9);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(1000000000u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_mul(x_13, x_15);
lean_dec(x_13);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_int_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_int_mul(x_11, x_15);
lean_dec(x_11);
x_20 = lean_int_add(x_19, x_12);
lean_dec(x_12);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed), 4, 3);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_10);
lean_closure_set(x_23, 2, x_15);
x_24 = lean_mk_thunk(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_2);
lean_ctor_set(x_25, 3, x_6);
return x_25;
}
block_29:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_5 = x_28;
goto block_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Time_ZonedDateTime_ofPlainDate___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_ZonedDateTime_ofPlainDate___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_38; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_3 = l_Std_Time_PlainTime_midnight;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_box(0);
x_9 = lean_box(1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_6);
x_12 = lean_unbox(x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_12);
x_13 = lean_unbox(x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 2, x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
lean_inc(x_15);
lean_inc(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_4);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_42);
x_43 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = l_Array_findFinIdx_x3f_loop___redArg(x_43, x_15, x_14);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_42);
x_45 = l_Array_back_x3f(lean_box(0), x_15);
lean_dec(x_15);
if (lean_obj_tag(x_45) == 0)
{
x_17 = x_11;
goto block_37;
}
else
{
lean_object* x_46; 
lean_dec(x_11);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_38 = x_46;
goto block_40;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_11);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_47, x_48);
x_50 = lean_array_fget(x_15, x_49);
lean_dec(x_49);
x_51 = lean_array_fget(x_15, x_47);
lean_dec(x_47);
lean_dec(x_15);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_nat_abs(x_54);
lean_dec(x_54);
x_56 = lean_nat_to_int(x_55);
x_57 = lean_int_sub(x_52, x_56);
lean_dec(x_56);
lean_dec(x_52);
x_58 = lean_int_dec_lt(x_42, x_57);
lean_dec(x_57);
lean_dec(x_42);
if (x_58 == 0)
{
lean_dec(x_50);
x_38 = x_51;
goto block_40;
}
else
{
lean_dec(x_51);
x_38 = x_50;
goto block_40;
}
}
block_37:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
lean_dec(x_17);
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_20 = lean_nat_to_int(x_14);
x_21 = l_Std_Time_TimeZone_toSeconds(x_18);
x_22 = lean_int_neg(x_21);
x_23 = lean_int_neg(x_20);
lean_dec(x_20);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(1000000000u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_mul(x_24, x_26);
lean_dec(x_24);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_int_add(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_30 = lean_int_mul(x_22, x_26);
lean_dec(x_22);
x_31 = lean_int_add(x_30, x_23);
lean_dec(x_23);
lean_dec(x_30);
x_32 = lean_int_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_33 = l_Std_Time_Duration_ofNanoseconds(x_32);
lean_dec(x_32);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed), 4, 3);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_21);
lean_closure_set(x_34, 2, x_26);
x_35 = lean_mk_thunk(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_16);
lean_ctor_set(x_36, 3, x_18);
return x_36;
}
block_40:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_17 = x_39;
goto block_37;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateWithZone___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_ofPlainDateWithZone(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDate___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_toPlainDate(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_toPlainTime(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_of(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_Database_defaultGetZoneRules(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_31; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
lean_inc(x_1);
x_34 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_findFinIdx_x3f_loop___redArg(x_36, x_37, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_35);
x_40 = l_Array_back_x3f(lean_box(0), x_37);
lean_dec(x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_5, 0);
lean_inc(x_41);
x_8 = x_41;
goto block_30;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_31 = x_42;
goto block_33;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_43, x_44);
x_46 = lean_array_fget(x_37, x_45);
lean_dec(x_45);
x_47 = lean_array_fget(x_37, x_43);
lean_dec(x_43);
lean_dec(x_37);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_nat_abs(x_50);
lean_dec(x_50);
x_52 = lean_nat_to_int(x_51);
x_53 = lean_int_sub(x_48, x_52);
lean_dec(x_52);
lean_dec(x_48);
x_54 = lean_int_dec_lt(x_35, x_53);
lean_dec(x_53);
lean_dec(x_35);
if (x_54 == 0)
{
lean_dec(x_46);
x_31 = x_47;
goto block_33;
}
else
{
lean_dec(x_47);
x_31 = x_46;
goto block_33;
}
}
block_30:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_8);
lean_dec(x_8);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_to_int(x_11);
x_13 = l_Std_Time_TimeZone_toSeconds(x_9);
x_14 = lean_int_neg(x_13);
x_15 = lean_int_neg(x_12);
lean_dec(x_12);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(1000000000u);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_mul(x_16, x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_int_add(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_int_mul(x_14, x_18);
lean_dec(x_14);
x_23 = lean_int_add(x_22, x_15);
lean_dec(x_15);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__0___boxed), 4, 3);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_13);
lean_closure_set(x_26, 2, x_18);
x_27 = lean_mk_thunk(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_5);
lean_ctor_set(x_28, 3, x_9);
if (lean_is_scalar(x_7)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_7;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
block_33:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_8 = x_32;
goto block_30;
}
}
else
{
uint8_t x_55; 
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
return x_4;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestamp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_22; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_1);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_findFinIdx_x3f_loop___redArg(x_27, x_28, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_26);
x_31 = l_Array_back_x3f(lean_box(0), x_28);
lean_dec(x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec(x_2);
x_3 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_22 = x_33;
goto block_24;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_2);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_34, x_35);
x_37 = lean_array_fget(x_28, x_36);
lean_dec(x_36);
x_38 = lean_array_fget(x_28, x_34);
lean_dec(x_34);
lean_dec(x_28);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_nat_abs(x_41);
lean_dec(x_41);
x_43 = lean_nat_to_int(x_42);
x_44 = lean_int_sub(x_39, x_43);
lean_dec(x_43);
lean_dec(x_39);
x_45 = lean_int_dec_lt(x_26, x_44);
lean_dec(x_44);
lean_dec(x_26);
if (x_45 == 0)
{
lean_dec(x_37);
x_22 = x_38;
goto block_24;
}
else
{
lean_dec(x_38);
x_22 = x_37;
goto block_24;
}
}
block_21:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_3);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = l_Std_Time_TimeZone_toSeconds(x_4);
lean_dec(x_4);
x_9 = lean_int_neg(x_8);
lean_dec(x_8);
x_10 = lean_int_neg(x_7);
lean_dec(x_7);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(1000000000u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_mul(x_11, x_13);
lean_dec(x_11);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_int_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_int_mul(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = lean_int_add(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
return x_20;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_3 = x_23;
goto block_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_22; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_3 = lean_unsigned_to_nat(0u);
x_25 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_1);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Array_findFinIdx_x3f_loop___redArg(x_28, x_25, x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_27);
x_30 = l_Array_back_x3f(lean_box(0), x_25);
lean_dec(x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_box(0);
x_35 = lean_box(1);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_inc(x_33);
lean_inc(x_31);
x_37 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_32);
x_38 = lean_unbox(x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 1, x_38);
x_39 = lean_unbox(x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*3 + 2, x_39);
x_4 = x_37;
goto block_21;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_22 = x_40;
goto block_24;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_41, x_42);
x_44 = lean_array_fget(x_25, x_43);
lean_dec(x_43);
x_45 = lean_array_fget(x_25, x_41);
lean_dec(x_41);
lean_dec(x_25);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_nat_abs(x_48);
lean_dec(x_48);
x_50 = lean_nat_to_int(x_49);
x_51 = lean_int_sub(x_46, x_50);
lean_dec(x_50);
lean_dec(x_46);
x_52 = lean_int_dec_lt(x_27, x_51);
lean_dec(x_51);
lean_dec(x_27);
if (x_52 == 0)
{
lean_dec(x_44);
x_22 = x_45;
goto block_24;
}
else
{
lean_dec(x_45);
x_22 = x_44;
goto block_24;
}
}
block_21:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_4);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_7 = lean_nat_to_int(x_3);
x_8 = l_Std_Time_TimeZone_toSeconds(x_5);
lean_dec(x_5);
x_9 = lean_int_neg(x_8);
lean_dec(x_8);
x_10 = lean_int_neg(x_7);
lean_dec(x_7);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(1000000000u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_mul(x_11, x_13);
lean_dec(x_11);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_int_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_int_mul(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = lean_int_add(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
return x_20;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_4 = x_23;
goto block_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toTimestampWithZone___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDateTime_toTimestampWithZone(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestamp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_24; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_3 = l_Std_Time_PlainTime_midnight;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_inc(x_4);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_28);
x_29 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_findFinIdx_x3f_loop___redArg(x_29, x_30, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_28);
x_33 = l_Array_back_x3f(lean_box(0), x_30);
lean_dec(x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_5 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_24 = x_35;
goto block_26;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_36, x_37);
x_39 = lean_array_fget(x_30, x_38);
lean_dec(x_38);
x_40 = lean_array_fget(x_30, x_36);
lean_dec(x_36);
lean_dec(x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_nat_abs(x_43);
lean_dec(x_43);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_int_sub(x_41, x_45);
lean_dec(x_45);
lean_dec(x_41);
x_47 = lean_int_dec_lt(x_28, x_46);
lean_dec(x_46);
lean_dec(x_28);
if (x_47 == 0)
{
lean_dec(x_39);
x_24 = x_40;
goto block_26;
}
else
{
lean_dec(x_40);
x_24 = x_39;
goto block_26;
}
}
block_23:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_5);
lean_dec(x_5);
x_7 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_to_int(x_8);
x_10 = l_Std_Time_TimeZone_toSeconds(x_6);
lean_dec(x_6);
x_11 = lean_int_neg(x_10);
lean_dec(x_10);
x_12 = lean_int_neg(x_9);
lean_dec(x_9);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(1000000000u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_mul(x_13, x_15);
lean_dec(x_13);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_int_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_int_mul(x_11, x_15);
lean_dec(x_15);
lean_dec(x_11);
x_20 = lean_int_add(x_19, x_12);
lean_dec(x_12);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
return x_22;
}
block_26:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_5 = x_25;
goto block_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_24; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_3 = l_Std_Time_PlainTime_midnight;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_27 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_4);
x_28 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDate___lam__1___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Array_findFinIdx_x3f_loop___redArg(x_30, x_27, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
x_32 = l_Array_back_x3f(lean_box(0), x_27);
lean_dec(x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_box(0);
x_37 = lean_box(1);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_33);
x_39 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_34);
x_40 = lean_unbox(x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_40);
x_41 = lean_unbox(x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 2, x_41);
x_6 = x_39;
goto block_23;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_24 = x_42;
goto block_26;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_43, x_44);
x_46 = lean_array_fget(x_27, x_45);
lean_dec(x_45);
x_47 = lean_array_fget(x_27, x_43);
lean_dec(x_43);
lean_dec(x_27);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_nat_abs(x_50);
lean_dec(x_50);
x_52 = lean_nat_to_int(x_51);
x_53 = lean_int_sub(x_48, x_52);
lean_dec(x_52);
lean_dec(x_48);
x_54 = lean_int_dec_lt(x_29, x_53);
lean_dec(x_53);
lean_dec(x_29);
if (x_54 == 0)
{
lean_dec(x_46);
x_24 = x_47;
goto block_26;
}
else
{
lean_dec(x_47);
x_24 = x_46;
goto block_26;
}
}
block_23:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_6);
lean_dec(x_6);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_9 = lean_nat_to_int(x_5);
x_10 = l_Std_Time_TimeZone_toSeconds(x_7);
lean_dec(x_7);
x_11 = lean_int_neg(x_10);
lean_dec(x_10);
x_12 = lean_int_neg(x_9);
lean_dec(x_9);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(1000000000u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_mul(x_13, x_15);
lean_dec(x_13);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_int_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_int_mul(x_11, x_15);
lean_dec(x_15);
lean_dec(x_11);
x_20 = lean_int_add(x_19, x_12);
lean_dec(x_12);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
return x_22;
}
block_26:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_6 = x_25;
goto block_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampWithZone___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_PlainDate_toTimestampWithZone(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Std_Time_Zoned_DateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_DateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZoneRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZonedDateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
