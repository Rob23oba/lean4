// Lean compiler output
// Module: Lean.Meta.ReduceEval
// Imports: Lean.Meta.Offset
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
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalName;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; 
x_47 = lean_box(1);
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get_uint8(x_48, 9);
x_50 = lean_unbox(x_47);
x_51 = l_Lean_Meta_TransparencyMode_lt(x_49, x_50);
if (x_51 == 0)
{
x_8 = x_49;
goto block_46;
}
else
{
uint8_t x_52; 
x_52 = lean_unbox(x_47);
x_8 = x_52;
goto block_46;
}
block_46:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint8(x_9, 0);
x_11 = lean_ctor_get_uint8(x_9, 1);
x_12 = lean_ctor_get_uint8(x_9, 2);
x_13 = lean_ctor_get_uint8(x_9, 3);
x_14 = lean_ctor_get_uint8(x_9, 4);
x_15 = lean_ctor_get_uint8(x_9, 5);
x_16 = lean_ctor_get_uint8(x_9, 6);
x_17 = lean_ctor_get_uint8(x_9, 7);
x_18 = lean_ctor_get_uint8(x_9, 8);
x_19 = lean_ctor_get_uint8(x_9, 10);
x_20 = lean_ctor_get_uint8(x_9, 11);
x_21 = lean_ctor_get_uint8(x_9, 12);
x_22 = lean_ctor_get_uint8(x_9, 13);
x_23 = lean_ctor_get_uint8(x_9, 14);
x_24 = lean_ctor_get_uint8(x_9, 15);
x_25 = lean_ctor_get_uint8(x_9, 16);
x_26 = lean_ctor_get_uint8(x_9, 17);
x_27 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_27, 0, x_10);
lean_ctor_set_uint8(x_27, 1, x_11);
lean_ctor_set_uint8(x_27, 2, x_12);
lean_ctor_set_uint8(x_27, 3, x_13);
lean_ctor_set_uint8(x_27, 4, x_14);
lean_ctor_set_uint8(x_27, 5, x_15);
lean_ctor_set_uint8(x_27, 6, x_16);
lean_ctor_set_uint8(x_27, 7, x_17);
lean_ctor_set_uint8(x_27, 8, x_18);
lean_ctor_set_uint8(x_27, 9, x_8);
lean_ctor_set_uint8(x_27, 10, x_19);
lean_ctor_set_uint8(x_27, 11, x_20);
lean_ctor_set_uint8(x_27, 12, x_21);
lean_ctor_set_uint8(x_27, 13, x_22);
lean_ctor_set_uint8(x_27, 14, x_23);
lean_ctor_set_uint8(x_27, 15, x_24);
lean_ctor_set_uint8(x_27, 16, x_25);
lean_ctor_set_uint8(x_27, 17, x_26);
x_28 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_shift_left(x_31, x_30);
x_33 = l_Lean_Meta_TransparencyMode_toUInt64(x_8);
x_34 = lean_uint64_lor(x_32, x_33);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_36 = lean_ctor_get(x_3, 1);
x_37 = lean_ctor_get(x_3, 2);
x_38 = lean_ctor_get(x_3, 3);
x_39 = lean_ctor_get(x_3, 4);
x_40 = lean_ctor_get(x_3, 5);
x_41 = lean_ctor_get(x_3, 6);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
x_44 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set_uint64(x_44, sizeof(void*)*7, x_34);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 8, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 9, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 10, x_43);
x_45 = lean_apply_6(x_1, x_2, x_44, x_4, x_5, x_6, x_7);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_reduceEval___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_reduceEval___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_reduceEval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_mk_string_unchecked("reduceEval: failed to evaluate argument", 39, 39);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = l_Lean_indentExpr(x_1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalNat___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Meta_evalNat(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalNat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalNat___lam__0), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_28; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_28 = l_Lean_Expr_getAppFn(x_9);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Expr_getAppNumArgs(x_9);
x_31 = lean_mk_string_unchecked("Option", 6, 6);
x_41 = lean_mk_string_unchecked("none", 4, 4);
lean_inc(x_31);
x_42 = l_Lean_Name_mkStr2(x_31, x_41);
x_43 = lean_name_eq(x_29, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
x_32 = x_43;
goto block_40;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_30, x_44);
x_32 = x_45;
goto block_40;
}
block_40:
{
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_11);
x_33 = lean_mk_string_unchecked("some", 4, 4);
x_34 = l_Lean_Name_mkStr2(x_31, x_33);
x_35 = lean_name_eq(x_29, x_34);
lean_dec(x_34);
lean_dec(x_29);
if (x_35 == 0)
{
lean_dec(x_30);
x_12 = x_35;
goto block_27;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_30, x_36);
lean_dec(x_30);
x_12 = x_37;
goto block_27;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_11;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_46 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_9, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
block_27:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_9, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_15 = l_Lean_Meta_reduceEval___redArg(x_1, x_14, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
return x_8;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_8);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___redArg___lam__0), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_instReduceEvalOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReduceEvalString___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 9)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_1, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalString___lam__0), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; 
x_66 = lean_box(1);
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get_uint8(x_67, 9);
x_69 = lean_unbox(x_66);
x_70 = l_Lean_Meta_TransparencyMode_lt(x_68, x_69);
if (x_70 == 0)
{
x_7 = x_68;
goto block_65;
}
else
{
uint8_t x_71; 
x_71 = lean_unbox(x_66);
x_7 = x_71;
goto block_65;
}
block_65:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_8, 0);
x_10 = lean_ctor_get_uint8(x_8, 1);
x_11 = lean_ctor_get_uint8(x_8, 2);
x_12 = lean_ctor_get_uint8(x_8, 3);
x_13 = lean_ctor_get_uint8(x_8, 4);
x_14 = lean_ctor_get_uint8(x_8, 5);
x_15 = lean_ctor_get_uint8(x_8, 6);
x_16 = lean_ctor_get_uint8(x_8, 7);
x_17 = lean_ctor_get_uint8(x_8, 8);
x_18 = lean_ctor_get_uint8(x_8, 10);
x_19 = lean_ctor_get_uint8(x_8, 11);
x_20 = lean_ctor_get_uint8(x_8, 12);
x_21 = lean_ctor_get_uint8(x_8, 13);
x_22 = lean_ctor_get_uint8(x_8, 14);
x_23 = lean_ctor_get_uint8(x_8, 15);
x_24 = lean_ctor_get_uint8(x_8, 16);
x_25 = lean_ctor_get_uint8(x_8, 17);
x_26 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_26, 0, x_9);
lean_ctor_set_uint8(x_26, 1, x_10);
lean_ctor_set_uint8(x_26, 2, x_11);
lean_ctor_set_uint8(x_26, 3, x_12);
lean_ctor_set_uint8(x_26, 4, x_13);
lean_ctor_set_uint8(x_26, 5, x_14);
lean_ctor_set_uint8(x_26, 6, x_15);
lean_ctor_set_uint8(x_26, 7, x_16);
lean_ctor_set_uint8(x_26, 8, x_17);
lean_ctor_set_uint8(x_26, 9, x_7);
lean_ctor_set_uint8(x_26, 10, x_18);
lean_ctor_set_uint8(x_26, 11, x_19);
lean_ctor_set_uint8(x_26, 12, x_20);
lean_ctor_set_uint8(x_26, 13, x_21);
lean_ctor_set_uint8(x_26, 14, x_22);
lean_ctor_set_uint8(x_26, 15, x_23);
lean_ctor_set_uint8(x_26, 16, x_24);
lean_ctor_set_uint8(x_26, 17, x_25);
x_27 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_shift_left(x_30, x_29);
x_32 = l_Lean_Meta_TransparencyMode_toUInt64(x_7);
x_33 = lean_uint64_lor(x_31, x_32);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_ctor_get(x_2, 4);
x_39 = lean_ctor_get(x_2, 5);
x_40 = lean_ctor_get(x_2, 6);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_43 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_37);
lean_ctor_set(x_43, 4, x_38);
lean_ctor_set(x_43, 5, x_39);
lean_ctor_set(x_43, 6, x_40);
lean_ctor_set_uint64(x_43, sizeof(void*)*7, x_33);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 8, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 9, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 10, x_42);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_43);
x_44 = lean_whnf(x_1, x_43, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_43);
lean_inc(x_45);
x_47 = l_Lean_Meta_evalNat(x_45, x_43, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_45, x_43, x_3, x_4, x_5, x_49);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_43);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_47, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
lean_ctor_set(x_47, 0, x_53);
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
return x_47;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_47);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_44);
if (x_61 == 0)
{
return x_44;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_44, 0);
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_44);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; 
x_62 = lean_box(1);
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get_uint8(x_63, 9);
x_65 = lean_unbox(x_62);
x_66 = l_Lean_Meta_TransparencyMode_lt(x_64, x_65);
if (x_66 == 0)
{
x_7 = x_64;
goto block_61;
}
else
{
uint8_t x_67; 
x_67 = lean_unbox(x_62);
x_7 = x_67;
goto block_61;
}
block_61:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_8, 0);
x_10 = lean_ctor_get_uint8(x_8, 1);
x_11 = lean_ctor_get_uint8(x_8, 2);
x_12 = lean_ctor_get_uint8(x_8, 3);
x_13 = lean_ctor_get_uint8(x_8, 4);
x_14 = lean_ctor_get_uint8(x_8, 5);
x_15 = lean_ctor_get_uint8(x_8, 6);
x_16 = lean_ctor_get_uint8(x_8, 7);
x_17 = lean_ctor_get_uint8(x_8, 8);
x_18 = lean_ctor_get_uint8(x_8, 10);
x_19 = lean_ctor_get_uint8(x_8, 11);
x_20 = lean_ctor_get_uint8(x_8, 12);
x_21 = lean_ctor_get_uint8(x_8, 13);
x_22 = lean_ctor_get_uint8(x_8, 14);
x_23 = lean_ctor_get_uint8(x_8, 15);
x_24 = lean_ctor_get_uint8(x_8, 16);
x_25 = lean_ctor_get_uint8(x_8, 17);
x_26 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_26, 0, x_9);
lean_ctor_set_uint8(x_26, 1, x_10);
lean_ctor_set_uint8(x_26, 2, x_11);
lean_ctor_set_uint8(x_26, 3, x_12);
lean_ctor_set_uint8(x_26, 4, x_13);
lean_ctor_set_uint8(x_26, 5, x_14);
lean_ctor_set_uint8(x_26, 6, x_15);
lean_ctor_set_uint8(x_26, 7, x_16);
lean_ctor_set_uint8(x_26, 8, x_17);
lean_ctor_set_uint8(x_26, 9, x_7);
lean_ctor_set_uint8(x_26, 10, x_18);
lean_ctor_set_uint8(x_26, 11, x_19);
lean_ctor_set_uint8(x_26, 12, x_20);
lean_ctor_set_uint8(x_26, 13, x_21);
lean_ctor_set_uint8(x_26, 14, x_22);
lean_ctor_set_uint8(x_26, 15, x_23);
lean_ctor_set_uint8(x_26, 16, x_24);
lean_ctor_set_uint8(x_26, 17, x_25);
x_27 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_shift_left(x_30, x_29);
x_32 = l_Lean_Meta_TransparencyMode_toUInt64(x_7);
x_33 = lean_uint64_lor(x_31, x_32);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_ctor_get(x_2, 4);
x_39 = lean_ctor_get(x_2, 5);
x_40 = lean_ctor_get(x_2, 6);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_43 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_37);
lean_ctor_set(x_43, 4, x_38);
lean_ctor_set(x_43, 5, x_39);
lean_ctor_set(x_43, 6, x_40);
lean_ctor_set_uint64(x_43, sizeof(void*)*7, x_33);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 8, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 9, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 10, x_42);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_43);
lean_inc(x_1);
x_44 = lean_whnf(x_1, x_43, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 9)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_1, x_43, x_3, x_4, x_5, x_47);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_43);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_dec(x_44);
x_56 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_1, x_43, x_3, x_4, x_5, x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_43);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_dec_eq(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = l_Lean_Expr_getAppFn(x_8);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_66; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_getAppNumArgs(x_8);
x_37 = lean_mk_string_unchecked("Lean", 4, 4);
x_38 = lean_mk_string_unchecked("Name", 4, 4);
x_75 = lean_mk_string_unchecked("anonymous", 9, 9);
lean_inc(x_38);
lean_inc(x_37);
x_76 = l_Lean_Name_mkStr3(x_37, x_38, x_75);
x_77 = lean_name_eq(x_12, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
x_66 = x_77;
goto block_74;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_13, x_78);
x_66 = x_79;
goto block_74;
}
block_36:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
x_15 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
lean_inc(x_17);
x_18 = l_Lean_Expr_getRevArg_x21(x_8, x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_18, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_sub(x_17, x_16);
lean_dec(x_17);
x_23 = l_Lean_Expr_getRevArg_x21(x_8, x_22);
lean_dec(x_8);
x_24 = l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(x_23, x_2, x_3, x_4, x_5, x_21);
lean_dec(x_2);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Lean_Name_num___override(x_20, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = l_Lean_Name_num___override(x_20, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_20);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
}
block_65:
{
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_mk_string_unchecked("num", 3, 3);
x_41 = l_Lean_Name_mkStr3(x_37, x_38, x_40);
x_42 = lean_name_eq(x_12, x_41);
lean_dec(x_41);
lean_dec(x_12);
if (x_42 == 0)
{
x_14 = x_42;
goto block_36;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(0);
x_44 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(x_13, x_43);
x_14 = x_44;
goto block_36;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_12);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_13, x_45);
lean_dec(x_13);
lean_inc(x_46);
x_47 = l_Lean_Expr_getRevArg_x21(x_8, x_46);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_48 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_47, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_nat_sub(x_46, x_45);
lean_dec(x_46);
x_52 = l_Lean_Expr_getRevArg_x21(x_8, x_51);
lean_dec(x_8);
x_53 = l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(x_52, x_2, x_3, x_4, x_5, x_50);
lean_dec(x_2);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = l_Lean_Name_str___override(x_49, x_55);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = l_Lean_Name_str___override(x_49, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_49);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_dec(x_46);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
}
}
block_74:
{
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_10);
x_67 = lean_mk_string_unchecked("str", 3, 3);
lean_inc(x_38);
lean_inc(x_37);
x_68 = l_Lean_Name_mkStr3(x_37, x_38, x_67);
x_69 = lean_name_eq(x_12, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
x_39 = x_69;
goto block_65;
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_box(0);
x_71 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(x_13, x_70);
x_39 = x_71;
goto block_65;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_10;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
return x_73;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_11);
lean_dec(x_10);
x_80 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___redArg(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_7);
if (x_81 == 0)
{
return x_7;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_7, 0);
x_83 = lean_ctor_get(x_7, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_7);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_reduceEval___at_____private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalName() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName), 6, 0);
return x_1;
}
}
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ReduceEval(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instReduceEvalNat = _init_l_Lean_Meta_instReduceEvalNat();
lean_mark_persistent(l_Lean_Meta_instReduceEvalNat);
l_Lean_Meta_instReduceEvalString = _init_l_Lean_Meta_instReduceEvalString();
lean_mark_persistent(l_Lean_Meta_instReduceEvalString);
l_Lean_Meta_instReduceEvalName = _init_l_Lean_Meta_instReduceEvalName();
lean_mark_persistent(l_Lean_Meta_instReduceEvalName);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
