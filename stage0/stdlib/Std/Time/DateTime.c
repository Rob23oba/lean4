// Lean compiler output
// Module: Std.Time.DateTime
// Imports: Std.Time.DateTime.Timestamp Std.Time.DateTime.PlainDateTime
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
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateTimeAssumingUTC(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
extern lean_object* l_Std_Time_PlainTime_midnight;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateTimeAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(86400u);
x_3 = lean_nat_to_int(x_2);
x_4 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_5 = lean_int_mul(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(86400u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_ediv(x_2, x_4);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Timestamp_toPlainDateAssumingUTC(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(1000000000u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_mul(x_2, x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_int_add(x_5, x_6);
lean_dec(x_5);
x_8 = l_Std_Time_PlainTime_ofNanoseconds(x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Timestamp_getTimeAssumingUTC(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(86400u);
x_3 = lean_nat_to_int(x_2);
x_4 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_5 = lean_int_mul(x_4, x_3);
lean_dec(x_3);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = lean_unsigned_to_nat(86400u);
x_4 = lean_nat_to_int(x_3);
x_5 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_6 = lean_int_mul(x_5, x_4);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_to_int(x_7);
x_9 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_2);
x_10 = lean_int_mul(x_9, x_4);
lean_dec(x_4);
lean_dec(x_9);
x_11 = lean_int_neg(x_10);
lean_dec(x_10);
x_12 = lean_int_neg(x_8);
x_13 = lean_unsigned_to_nat(1000000000u);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_mul(x_6, x_14);
lean_dec(x_6);
x_16 = lean_int_add(x_15, x_8);
lean_dec(x_8);
lean_dec(x_15);
x_17 = lean_int_mul(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
x_18 = lean_int_add(x_17, x_12);
lean_dec(x_12);
lean_dec(x_17);
x_19 = lean_int_add(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
return x_20;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_PlainDate_instHSubDuration___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Time_PlainTime_midnight;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toPlainDate(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_unsigned_to_nat(11u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_add(x_3, x_5);
lean_dec(x_5);
x_7 = lean_int_sub(x_6, x_3);
lean_dec(x_6);
x_8 = lean_int_add(x_7, x_3);
lean_dec(x_7);
x_9 = lean_int_sub(x_3, x_3);
x_10 = lean_int_emod(x_9, x_8);
x_11 = lean_int_add(x_10, x_8);
lean_dec(x_10);
x_12 = lean_int_emod(x_11, x_8);
lean_dec(x_8);
lean_dec(x_11);
x_13 = lean_int_add(x_12, x_3);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(30u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_add(x_3, x_15);
lean_dec(x_15);
x_17 = lean_int_sub(x_16, x_3);
lean_dec(x_16);
x_18 = lean_int_add(x_17, x_3);
lean_dec(x_17);
x_19 = lean_int_emod(x_9, x_18);
lean_dec(x_9);
x_20 = lean_int_add(x_19, x_18);
lean_dec(x_19);
x_21 = lean_int_emod(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
x_22 = lean_int_add(x_21, x_3);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toPlainTime(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_4 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_int_neg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_int_neg(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(1000000000u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_int_add(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_int_mul(x_6, x_11);
lean_dec(x_11);
lean_dec(x_6);
x_16 = lean_int_add(x_15, x_8);
lean_dec(x_8);
lean_dec(x_15);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_Duration_ofNanoseconds(x_17);
lean_dec(x_17);
return x_18;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_instHSubDuration() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_instHSubDuration___lam__0), 2, 0);
return x_1;
}
}
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime_Timestamp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_PlainDate_instHSubDuration = _init_l_Std_Time_PlainDate_instHSubDuration();
lean_mark_persistent(l_Std_Time_PlainDate_instHSubDuration);
l_Std_Time_PlainDateTime_instHSubDuration = _init_l_Std_Time_PlainDateTime_instHSubDuration();
lean_mark_persistent(l_Std_Time_PlainDateTime_instHSubDuration);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
