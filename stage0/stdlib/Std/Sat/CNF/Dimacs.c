// Lean compiler output
// Module: Std.Sat.CNF.Dimacs
// Imports: Std.Sat.CNF.Basic Std.Sat.CNF.RelabelFin
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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses___boxed(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_box(0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
x_33 = lean_nat_dec_le(x_31, x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
x_16 = x_2;
goto block_29;
}
else
{
lean_dec(x_31);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_30);
x_16 = x_2;
goto block_29;
}
block_15:
{
lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; 
x_10 = lean_string_append(x_1, x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(32u);
x_12 = l_Char_ofNat(x_11);
x_13 = lean_string_push(x_10, x_12);
x_1 = x_13;
x_2 = x_7;
x_3 = x_8;
goto _start;
}
block_29:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_mk_string_unchecked("-", 1, 1);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_20);
x_23 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_24 = lean_string_append(x_19, x_23);
lean_dec(x_23);
x_8 = x_16;
x_9 = x_24;
goto block_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_8 = x_16;
x_9 = x_28;
goto block_15;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_44; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_ctor_get(x_34, 0);
lean_inc(x_60);
x_61 = lean_nat_dec_le(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
x_44 = x_62;
goto block_57;
}
else
{
lean_object* x_63; 
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_60);
x_44 = x_63;
goto block_57;
}
block_43:
{
lean_object* x_38; lean_object* x_39; uint32_t x_40; lean_object* x_41; 
x_38 = lean_string_append(x_1, x_37);
lean_dec(x_37);
x_39 = lean_unsigned_to_nat(32u);
x_40 = l_Char_ofNat(x_39);
x_41 = lean_string_push(x_38, x_40);
x_1 = x_41;
x_2 = x_35;
x_3 = x_36;
goto _start;
}
block_57:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_mk_string_unchecked("-", 1, 1);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_48, x_49);
lean_dec(x_48);
x_51 = l___private_Init_Data_Repr_0__Nat_reprFast(x_50);
x_52 = lean_string_append(x_47, x_51);
lean_dec(x_51);
x_36 = x_44;
x_37 = x_52;
goto block_43;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
lean_dec(x_34);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_53, x_54);
lean_dec(x_53);
x_56 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_36 = x_44;
x_37 = x_56;
goto block_43;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
x_12 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(x_1, x_6, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(48u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_string_push(x_13, x_16);
x_18 = lean_unsigned_to_nat(10u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_string_push(x_17, x_19);
x_1 = x_20;
x_2 = x_7;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_24);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__0(x_1, x_22, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(48u);
x_33 = l_Char_ofNat(x_32);
x_34 = lean_string_push(x_30, x_33);
x_35 = lean_unsigned_to_nat(10u);
x_36 = l_Char_ofNat(x_35);
x_37 = lean_string_push(x_34, x_36);
x_1 = x_37;
x_2 = x_23;
x_3 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = l_List_foldlM___at___Std_Sat_CNF_dimacs_go_spec__1(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_Std_Sat_CNF_dimacs_go(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_mk_string_unchecked("p cnf ", 6, 6);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = lean_string_append(x_7, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked(" ", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_mk_string_unchecked("\n", 1, 1);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_5);
lean_dec(x_5);
return x_20;
}
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_RelabelFin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
