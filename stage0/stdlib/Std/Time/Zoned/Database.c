// Lean compiler output
// Module: Std.Time.Zoned.Database
// Imports: Std.Time.Zoned.ZonedDateTime Std.Time.Zoned.Database.Basic Std.Time.Zoned.Database.TZdb Std.Time.Zoned.Database.Windows Init.System.Platform
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_Std_Time_Database_TZdb_localRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_int64_neg(uint64_t);
uint64_t lean_int64_of_nat(lean_object*);
lean_object* lean_get_windows_local_timezone_id_at(uint64_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Std_Time_Database_TZdb_readRulesFromDisk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Time_Database_defaultGetZoneRules_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* l_Std_Time_Database_Windows_getZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Time_Database_defaultGetZoneRules_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_4);
x_10 = l_System_FilePath_pathExists(x_9, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_9);
x_16 = lean_box(0);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_10;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_9, x_1, x_13);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_24);
lean_ctor_set(x_21, 0, x_10);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_10);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_box(0);
x_36 = lean_unbox(x_33);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
lean_dec(x_9);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_add(x_4, x_40);
x_4 = x_41;
x_5 = x_38;
x_6 = x_34;
goto _start;
}
else
{
lean_object* x_43; 
x_43 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_9, x_1, x_34);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetZoneRules(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_System_Platform_isWindows;
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_mk_string_unchecked("/usr/share/zoneinfo", 19, 19);
x_5 = lean_mk_string_unchecked("/share/zoneinfo", 15, 15);
x_6 = lean_unsigned_to_nat(4u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_mk_string_unchecked("TZDIR", 5, 5);
x_10 = lean_io_getenv(x_9, x_2);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_mk_string_unchecked("/etc/zoneinfo", 13, 13);
x_16 = lean_array_push(x_8, x_5);
x_17 = lean_mk_string_unchecked("/usr/share/lib/zoneinfo", 23, 23);
x_18 = lean_array_push(x_16, x_15);
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_box(0);
x_21 = lean_box(0);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_20);
x_22 = lean_array_size(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
lean_inc(x_1);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Std_Time_Database_defaultGetZoneRules_spec__0(x_1, x_19, x_22, x_24, x_10, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_mk_string_unchecked("cannot find ", 12, 12);
x_31 = lean_string_append(x_30, x_1);
lean_dec(x_1);
x_32 = lean_mk_string_unchecked(" in the local timezone database", 31, 31);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_mk_string_unchecked("cannot find ", 12, 12);
x_37 = lean_string_append(x_36, x_1);
lean_dec(x_1);
x_38 = lean_mk_string_unchecked(" in the local timezone database", 31, 31);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_25, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_44);
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_ctor_get(x_27, 0);
lean_inc(x_46);
lean_dec(x_27);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; lean_object* x_62; size_t x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_dec(x_10);
x_53 = lean_mk_string_unchecked("/etc/zoneinfo", 13, 13);
x_54 = lean_array_push(x_8, x_5);
x_55 = lean_mk_string_unchecked("/usr/share/lib/zoneinfo", 23, 23);
x_56 = lean_array_push(x_54, x_53);
x_57 = lean_array_push(x_56, x_55);
x_58 = lean_box(0);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_size(x_57);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_usize_of_nat(x_62);
lean_inc(x_1);
x_64 = l_Array_forIn_x27Unsafe_loop___at___Std_Time_Database_defaultGetZoneRules_spec__0(x_1, x_57, x_61, x_63, x_60, x_52);
lean_dec(x_57);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = lean_mk_string_unchecked("cannot find ", 12, 12);
x_70 = lean_string_append(x_69, x_1);
lean_dec(x_1);
x_71 = lean_mk_string_unchecked(" in the local timezone database", 31, 31);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_is_scalar(x_68)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_68;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_67);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
lean_dec(x_66);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_64, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_81 = x_64;
} else {
 lean_dec_ref(x_64);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_8);
lean_dec(x_5);
x_83 = lean_ctor_get(x_10, 1);
lean_inc(x_83);
lean_dec(x_10);
x_84 = lean_ctor_get(x_11, 0);
lean_inc(x_84);
lean_dec(x_11);
x_85 = l_Std_Time_Database_TZdb_readRulesFromDisk(x_84, x_1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; 
x_86 = l_Std_Time_Database_Windows_getZoneRules(x_1, x_2);
lean_dec(x_1);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Time_Database_defaultGetZoneRules_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Std_Time_Database_defaultGetZoneRules_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Database_defaultGetLocalZoneRules(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("/etc/localtime", 14, 14);
x_4 = l_Std_Time_Database_TZdb_localRules(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(2147483648u);
x_6 = lean_int64_of_nat(x_5);
x_7 = lean_int64_neg(x_6);
x_8 = lean_get_windows_local_timezone_id_at(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_Time_Database_Windows_getZoneRules(x_9, x_10);
lean_dec(x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
lean_object* initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_TZdb(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_Database_Windows(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Platform(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_Database(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZonedDateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_TZdb(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_Database_Windows(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
