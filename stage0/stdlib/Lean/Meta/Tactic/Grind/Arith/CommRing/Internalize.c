// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize
// Imports: Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
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
lean_object* l_Lean_Meta_Grind_markAsCommRingTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_13 = lean_mk_string_unchecked("IntCast", 7, 7);
x_14 = lean_mk_string_unchecked("intCast", 7, 7);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = l_Lean_Expr_isConstOf(x_12, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_mk_string_unchecked("NatCast", 7, 7);
x_18 = lean_mk_string_unchecked("natCast", 7, 7);
x_19 = l_Lean_Name_mkStr2(x_17, x_18);
x_20 = l_Lean_Expr_isConstOf(x_12, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_mk_string_unchecked("OfNat", 5, 5);
x_22 = lean_mk_string_unchecked("ofNat", 5, 5);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = l_Lean_Expr_isConstOf(x_12, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_mk_string_unchecked("Neg", 3, 3);
x_26 = lean_mk_string_unchecked("neg", 3, 3);
x_27 = l_Lean_Name_mkStr2(x_25, x_26);
x_28 = l_Lean_Expr_isConstOf(x_12, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_11);
x_29 = l_Lean_Expr_isApp(x_12);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_12);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_31);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_35 = l_Lean_Expr_isApp(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
lean_dec(x_31);
x_36 = lean_box(0);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = l_Lean_Expr_appFnCleanup___redArg(x_34);
x_39 = lean_mk_string_unchecked("HPow", 4, 4);
x_40 = lean_mk_string_unchecked("hPow", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_Expr_isConstOf(x_38, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_31);
x_43 = lean_mk_string_unchecked("HMul", 4, 4);
x_44 = lean_mk_string_unchecked("hMul", 4, 4);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
x_46 = l_Lean_Expr_isConstOf(x_38, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_mk_string_unchecked("HSub", 4, 4);
x_48 = lean_mk_string_unchecked("hSub", 4, 4);
x_49 = l_Lean_Name_mkStr2(x_47, x_48);
x_50 = l_Lean_Expr_isConstOf(x_38, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_mk_string_unchecked("HAdd", 4, 4);
x_52 = lean_mk_string_unchecked("hAdd", 4, 4);
x_53 = l_Lean_Name_mkStr2(x_51, x_52);
x_54 = l_Lean_Expr_isConstOf(x_38, x_53);
lean_dec(x_53);
lean_dec(x_38);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_37);
x_55 = lean_box(0);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_37);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_37);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec(x_38);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_37);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_38);
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
lean_dec(x_31);
x_60 = l_Lean_Expr_cleanupAnnotations(x_59);
x_61 = lean_mk_string_unchecked("Nat", 3, 3);
x_62 = l_Lean_Name_mkStr1(x_61);
x_63 = l_Lean_Expr_isConstOf(x_60, x_62);
lean_dec(x_62);
lean_dec(x_60);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_37);
x_64 = lean_box(0);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_37);
return x_65;
}
}
}
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_12);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_11);
return x_66;
}
}
else
{
lean_object* x_67; 
lean_dec(x_12);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_11);
return x_67;
}
}
else
{
lean_object* x_68; 
lean_dec(x_12);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_11);
return x_68;
}
}
else
{
lean_object* x_69; 
lean_dec(x_12);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_11);
return x_69;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_5);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 12);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_checkTraceOption(x_4, x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(x_1, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_float_of_nat(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_27);
x_28 = lean_mk_empty_array_with_capacity(x_22);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_15);
lean_ctor_set(x_11, 1, x_29);
lean_ctor_set(x_11, 0, x_15);
x_30 = l_Lean_PersistentArray_push___redArg(x_21, x_11);
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_20);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 7);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_6, x_36, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_ctor_get(x_5, 5);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_50, sizeof(void*)*1);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_float_of_nat(x_53);
x_55 = lean_box(0);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_float(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_57, sizeof(void*)*2 + 8, x_54);
x_58 = lean_unbox(x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 16, x_58);
x_59 = lean_mk_empty_array_with_capacity(x_53);
x_60 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentArray_push___redArg(x_52, x_61);
x_63 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint64(x_63, sizeof(void*)*1, x_51);
x_64 = lean_ctor_get(x_44, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 7);
lean_inc(x_67);
lean_dec(x_44);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_45);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_11);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_257; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_257 = lean_ctor_get_uint8(x_121, sizeof(void*)*7 + 16);
lean_dec(x_121);
if (x_257 == 0)
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_124, sizeof(void*)*7 + 17);
lean_dec(x_124);
if (x_258 == 0)
{
lean_object* x_259; 
lean_dec(x_126);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_box(0);
lean_ctor_set(x_119, 1, x_125);
lean_ctor_set(x_119, 0, x_259);
return x_119;
}
else
{
lean_free_object(x_119);
goto block_256;
}
}
else
{
lean_dec(x_124);
lean_free_object(x_119);
goto block_256;
}
block_256:
{
lean_object* x_127; 
lean_inc(x_1);
x_127 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(x_1);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_126;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
return x_129;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_dec(x_127);
x_131 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(x_2);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_126);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_132 = l_Lean_Meta_Grind_Arith_CommRing_getRingId_x3f(x_130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_125);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_132, 0);
lean_dec(x_135);
x_136 = lean_box(0);
lean_ctor_set(x_132, 0, x_136);
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_dec(x_132);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_132, 1);
lean_inc(x_140);
lean_dec(x_132);
x_141 = lean_ctor_get(x_133, 0);
lean_inc(x_141);
lean_dec(x_133);
lean_inc(x_141);
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_131);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_142);
lean_inc(x_1);
x_143 = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(x_1, x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_140);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
x_147 = lean_box(0);
lean_ctor_set(x_143, 0, x_147);
return x_143;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_143, 1);
lean_inc(x_151);
lean_dec(x_143);
x_152 = !lean_is_exclusive(x_144);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_153 = lean_ctor_get(x_144, 0);
x_154 = lean_mk_string_unchecked("grind", 5, 5);
x_155 = lean_mk_string_unchecked("ring", 4, 4);
x_156 = lean_mk_string_unchecked("internalize", 11, 11);
x_157 = l_Lean_Name_mkStr3(x_154, x_155, x_156);
lean_inc(x_157);
x_158 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(x_157, x_9, x_151);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unbox(x_159);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_157);
lean_free_object(x_144);
lean_dec(x_141);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_49 = x_153;
x_50 = x_142;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_161;
goto block_118;
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_158);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_158, 1);
x_164 = lean_ctor_get(x_158, 0);
lean_dec(x_164);
x_165 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_163);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_167 = lean_ctor_get(x_165, 1);
x_168 = lean_ctor_get(x_165, 0);
lean_dec(x_168);
x_169 = lean_mk_string_unchecked("[", 1, 1);
x_170 = l_Lean_stringToMessageData(x_169);
lean_dec(x_169);
x_171 = l___private_Init_Data_Repr_0__Nat_reprFast(x_141);
lean_ctor_set_tag(x_144, 3);
lean_ctor_set(x_144, 0, x_171);
x_172 = l_Lean_MessageData_ofFormat(x_144);
lean_ctor_set_tag(x_165, 7);
lean_ctor_set(x_165, 1, x_172);
lean_ctor_set(x_165, 0, x_170);
x_173 = lean_mk_string_unchecked("]: ", 3, 3);
x_174 = l_Lean_stringToMessageData(x_173);
lean_dec(x_173);
lean_ctor_set_tag(x_158, 7);
lean_ctor_set(x_158, 1, x_174);
lean_ctor_set(x_158, 0, x_165);
lean_inc(x_1);
x_175 = l_Lean_MessageData_ofExpr(x_1);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_158);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_mk_string_unchecked("", 0, 0);
x_178 = l_Lean_stringToMessageData(x_177);
lean_dec(x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(x_157, x_179, x_7, x_8, x_9, x_10, x_167);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_49 = x_153;
x_50 = x_142;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_181;
goto block_118;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_182 = lean_ctor_get(x_165, 1);
lean_inc(x_182);
lean_dec(x_165);
x_183 = lean_mk_string_unchecked("[", 1, 1);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = l___private_Init_Data_Repr_0__Nat_reprFast(x_141);
lean_ctor_set_tag(x_144, 3);
lean_ctor_set(x_144, 0, x_185);
x_186 = l_Lean_MessageData_ofFormat(x_144);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_mk_string_unchecked("]: ", 3, 3);
x_189 = l_Lean_stringToMessageData(x_188);
lean_dec(x_188);
lean_ctor_set_tag(x_158, 7);
lean_ctor_set(x_158, 1, x_189);
lean_ctor_set(x_158, 0, x_187);
lean_inc(x_1);
x_190 = l_Lean_MessageData_ofExpr(x_1);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_158);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_mk_string_unchecked("", 0, 0);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(x_157, x_194, x_7, x_8, x_9, x_10, x_182);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_49 = x_153;
x_50 = x_142;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_196;
goto block_118;
}
}
else
{
lean_free_object(x_158);
lean_dec(x_157);
lean_free_object(x_144);
lean_dec(x_153);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_165;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_158, 1);
lean_inc(x_197);
lean_dec(x_158);
x_198 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
x_201 = lean_mk_string_unchecked("[", 1, 1);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
x_203 = l___private_Init_Data_Repr_0__Nat_reprFast(x_141);
lean_ctor_set_tag(x_144, 3);
lean_ctor_set(x_144, 0, x_203);
x_204 = l_Lean_MessageData_ofFormat(x_144);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(7, 2, 0);
} else {
 x_205 = x_200;
 lean_ctor_set_tag(x_205, 7);
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_mk_string_unchecked("]: ", 3, 3);
x_207 = l_Lean_stringToMessageData(x_206);
lean_dec(x_206);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_207);
lean_inc(x_1);
x_209 = l_Lean_MessageData_ofExpr(x_1);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("", 0, 0);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(x_157, x_213, x_7, x_8, x_9, x_10, x_199);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_49 = x_153;
x_50 = x_142;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_215;
goto block_118;
}
else
{
lean_dec(x_157);
lean_free_object(x_144);
lean_dec(x_153);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_198;
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_216 = lean_ctor_get(x_144, 0);
lean_inc(x_216);
lean_dec(x_144);
x_217 = lean_mk_string_unchecked("grind", 5, 5);
x_218 = lean_mk_string_unchecked("ring", 4, 4);
x_219 = lean_mk_string_unchecked("internalize", 11, 11);
x_220 = l_Lean_Name_mkStr3(x_217, x_218, x_219);
lean_inc(x_220);
x_221 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(x_220, x_9, x_151);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_220);
lean_dec(x_141);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_49 = x_216;
x_50 = x_142;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_224;
goto block_118;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_226 = x_221;
} else {
 lean_dec_ref(x_221);
 x_226 = lean_box(0);
}
x_227 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
x_230 = lean_mk_string_unchecked("[", 1, 1);
x_231 = l_Lean_stringToMessageData(x_230);
lean_dec(x_230);
x_232 = l___private_Init_Data_Repr_0__Nat_reprFast(x_141);
x_233 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_234 = l_Lean_MessageData_ofFormat(x_233);
if (lean_is_scalar(x_229)) {
 x_235 = lean_alloc_ctor(7, 2, 0);
} else {
 x_235 = x_229;
 lean_ctor_set_tag(x_235, 7);
}
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_mk_string_unchecked("]: ", 3, 3);
x_237 = l_Lean_stringToMessageData(x_236);
lean_dec(x_236);
if (lean_is_scalar(x_226)) {
 x_238 = lean_alloc_ctor(7, 2, 0);
} else {
 x_238 = x_226;
 lean_ctor_set_tag(x_238, 7);
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_1);
x_239 = l_Lean_MessageData_ofExpr(x_1);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_mk_string_unchecked("", 0, 0);
x_242 = l_Lean_stringToMessageData(x_241);
lean_dec(x_241);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(x_220, x_243, x_7, x_8, x_9, x_10, x_228);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_49 = x_216;
x_50 = x_142;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_245;
goto block_118;
}
else
{
lean_dec(x_226);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_227;
}
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_143);
if (x_246 == 0)
{
return x_143;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_143, 0);
x_248 = lean_ctor_get(x_143, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_143);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_132);
if (x_250 == 0)
{
return x_132;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_132, 0);
x_252 = lean_ctor_get(x_132, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_132);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_130);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_254 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_126;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_125);
return x_255;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_329; 
x_260 = lean_ctor_get(x_119, 0);
x_261 = lean_ctor_get(x_119, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_119);
x_262 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
x_329 = lean_ctor_get_uint8(x_260, sizeof(void*)*7 + 16);
lean_dec(x_260);
if (x_329 == 0)
{
uint8_t x_330; 
x_330 = lean_ctor_get_uint8(x_263, sizeof(void*)*7 + 17);
lean_dec(x_263);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_265);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_331 = lean_box(0);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_264);
return x_332;
}
else
{
goto block_328;
}
}
else
{
lean_dec(x_263);
goto block_328;
}
block_328:
{
lean_object* x_266; 
lean_inc(x_1);
x_266 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(x_1);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_265;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_264);
return x_268;
}
else
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_266, 0);
lean_inc(x_269);
lean_dec(x_266);
x_270 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(x_2);
if (x_270 == 0)
{
lean_object* x_271; 
lean_dec(x_265);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_271 = l_Lean_Meta_Grind_Arith_CommRing_getRingId_x3f(x_269, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_264);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
x_275 = lean_box(0);
if (lean_is_scalar(x_274)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_274;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_273);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_271, 1);
lean_inc(x_277);
lean_dec(x_271);
x_278 = lean_ctor_get(x_272, 0);
lean_inc(x_278);
lean_dec(x_272);
lean_inc(x_278);
x_279 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set_uint8(x_279, sizeof(void*)*1, x_270);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_279);
lean_inc(x_1);
x_280 = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(x_1, x_279, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_277);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
x_284 = lean_box(0);
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_282);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_286 = lean_ctor_get(x_280, 1);
lean_inc(x_286);
lean_dec(x_280);
x_287 = lean_ctor_get(x_281, 0);
lean_inc(x_287);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 x_288 = x_281;
} else {
 lean_dec_ref(x_281);
 x_288 = lean_box(0);
}
x_289 = lean_mk_string_unchecked("grind", 5, 5);
x_290 = lean_mk_string_unchecked("ring", 4, 4);
x_291 = lean_mk_string_unchecked("internalize", 11, 11);
x_292 = l_Lean_Name_mkStr3(x_289, x_290, x_291);
lean_inc(x_292);
x_293 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(x_292, x_9, x_286);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_unbox(x_294);
lean_dec(x_294);
if (x_295 == 0)
{
lean_object* x_296; 
lean_dec(x_292);
lean_dec(x_288);
lean_dec(x_278);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec(x_293);
x_49 = x_287;
x_50 = x_279;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_296;
goto block_118;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_293, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_298 = x_293;
} else {
 lean_dec_ref(x_293);
 x_298 = lean_box(0);
}
x_299 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_297);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_301 = x_299;
} else {
 lean_dec_ref(x_299);
 x_301 = lean_box(0);
}
x_302 = lean_mk_string_unchecked("[", 1, 1);
x_303 = l_Lean_stringToMessageData(x_302);
lean_dec(x_302);
x_304 = l___private_Init_Data_Repr_0__Nat_reprFast(x_278);
if (lean_is_scalar(x_288)) {
 x_305 = lean_alloc_ctor(3, 1, 0);
} else {
 x_305 = x_288;
 lean_ctor_set_tag(x_305, 3);
}
lean_ctor_set(x_305, 0, x_304);
x_306 = l_Lean_MessageData_ofFormat(x_305);
if (lean_is_scalar(x_301)) {
 x_307 = lean_alloc_ctor(7, 2, 0);
} else {
 x_307 = x_301;
 lean_ctor_set_tag(x_307, 7);
}
lean_ctor_set(x_307, 0, x_303);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_mk_string_unchecked("]: ", 3, 3);
x_309 = l_Lean_stringToMessageData(x_308);
lean_dec(x_308);
if (lean_is_scalar(x_298)) {
 x_310 = lean_alloc_ctor(7, 2, 0);
} else {
 x_310 = x_298;
 lean_ctor_set_tag(x_310, 7);
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_309);
lean_inc(x_1);
x_311 = l_Lean_MessageData_ofExpr(x_1);
x_312 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_mk_string_unchecked("", 0, 0);
x_314 = l_Lean_stringToMessageData(x_313);
lean_dec(x_313);
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(x_292, x_315, x_7, x_8, x_9, x_10, x_300);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_49 = x_287;
x_50 = x_279;
x_51 = x_3;
x_52 = x_4;
x_53 = x_5;
x_54 = x_6;
x_55 = x_7;
x_56 = x_8;
x_57 = x_9;
x_58 = x_10;
x_59 = x_317;
goto block_118;
}
else
{
lean_dec(x_298);
lean_dec(x_292);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_299;
}
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_318 = lean_ctor_get(x_280, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_280, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_320 = x_280;
} else {
 lean_dec_ref(x_280);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_322 = lean_ctor_get(x_271, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_271, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_324 = x_271;
} else {
 lean_dec_ref(x_271);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_269);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_326 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_265;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_264);
return x_327;
}
}
}
}
block_48:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 3);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_ctor_get(x_28, 15);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_18);
lean_ctor_set(x_40, 2, x_21);
lean_ctor_set(x_40, 3, x_32);
lean_ctor_set(x_40, 4, x_20);
lean_ctor_set(x_40, 5, x_30);
lean_ctor_set(x_40, 6, x_13);
lean_ctor_set(x_40, 7, x_27);
lean_ctor_set(x_40, 8, x_12);
lean_ctor_set(x_40, 9, x_15);
lean_ctor_set(x_40, 10, x_26);
lean_ctor_set(x_40, 11, x_17);
lean_ctor_set(x_40, 12, x_22);
lean_ctor_set(x_40, 13, x_14);
lean_ctor_set(x_40, 14, x_38);
lean_ctor_set(x_40, 15, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*16, x_31);
x_41 = lean_st_ref_set(x_24, x_40, x_19);
lean_dec(x_24);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
block_118:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc(x_50);
lean_inc(x_1);
x_60 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_51);
lean_inc(x_1);
x_62 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_51, x_52, x_53, x_54, x_55, x_56, x_57, x_58, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_take(x_51, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_50, 0);
lean_inc(x_67);
lean_dec(x_50);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_65, 7);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_65, sizeof(void*)*16);
x_77 = lean_ctor_get(x_65, 8);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 9);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 10);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 11);
lean_inc(x_80);
x_81 = lean_ctor_get(x_65, 12);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 13);
lean_inc(x_82);
x_83 = lean_ctor_get(x_65, 14);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 2);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_array_get_size(x_87);
x_89 = lean_nat_dec_lt(x_67, x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_dec(x_67);
lean_dec(x_49);
lean_dec(x_1);
x_12 = x_77;
x_13 = x_74;
x_14 = x_82;
x_15 = x_78;
x_16 = x_84;
x_17 = x_80;
x_18 = x_69;
x_19 = x_66;
x_20 = x_72;
x_21 = x_70;
x_22 = x_81;
x_23 = x_85;
x_24 = x_51;
x_25 = x_68;
x_26 = x_79;
x_27 = x_75;
x_28 = x_65;
x_29 = x_86;
x_30 = x_73;
x_31 = x_76;
x_32 = x_71;
x_33 = x_87;
goto block_48;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_90 = lean_array_fget(x_87, x_67);
x_91 = lean_box(0);
x_92 = lean_array_fset(x_87, x_67, x_91);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_90, 5);
lean_inc(x_98);
x_99 = lean_ctor_get(x_90, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_90, 7);
lean_inc(x_100);
x_101 = lean_ctor_get(x_90, 8);
lean_inc(x_101);
x_102 = lean_ctor_get(x_90, 9);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 10);
lean_inc(x_103);
x_104 = lean_ctor_get(x_90, 11);
lean_inc(x_104);
x_105 = lean_ctor_get(x_90, 12);
lean_inc(x_105);
x_106 = lean_ctor_get(x_90, 13);
lean_inc(x_106);
x_107 = lean_ctor_get(x_90, 14);
lean_inc(x_107);
x_108 = lean_ctor_get(x_90, 15);
lean_inc(x_108);
x_109 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(x_108, x_1, x_49);
x_110 = lean_ctor_get(x_90, 16);
lean_inc(x_110);
x_111 = lean_ctor_get(x_90, 17);
lean_inc(x_111);
x_112 = lean_ctor_get(x_90, 18);
lean_inc(x_112);
x_113 = lean_ctor_get(x_90, 19);
lean_inc(x_113);
x_114 = lean_ctor_get(x_90, 20);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_90, sizeof(void*)*21);
lean_dec(x_90);
x_116 = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(x_116, 0, x_93);
lean_ctor_set(x_116, 1, x_94);
lean_ctor_set(x_116, 2, x_95);
lean_ctor_set(x_116, 3, x_96);
lean_ctor_set(x_116, 4, x_97);
lean_ctor_set(x_116, 5, x_98);
lean_ctor_set(x_116, 6, x_99);
lean_ctor_set(x_116, 7, x_100);
lean_ctor_set(x_116, 8, x_101);
lean_ctor_set(x_116, 9, x_102);
lean_ctor_set(x_116, 10, x_103);
lean_ctor_set(x_116, 11, x_104);
lean_ctor_set(x_116, 12, x_105);
lean_ctor_set(x_116, 13, x_106);
lean_ctor_set(x_116, 14, x_107);
lean_ctor_set(x_116, 15, x_109);
lean_ctor_set(x_116, 16, x_110);
lean_ctor_set(x_116, 17, x_111);
lean_ctor_set(x_116, 18, x_112);
lean_ctor_set(x_116, 19, x_113);
lean_ctor_set(x_116, 20, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*21, x_115);
x_117 = lean_array_fset(x_92, x_67, x_116);
lean_dec(x_67);
x_12 = x_77;
x_13 = x_74;
x_14 = x_82;
x_15 = x_78;
x_16 = x_84;
x_17 = x_80;
x_18 = x_69;
x_19 = x_66;
x_20 = x_72;
x_21 = x_70;
x_22 = x_81;
x_23 = x_85;
x_24 = x_51;
x_25 = x_68;
x_26 = x_79;
x_27 = x_75;
x_28 = x_65;
x_29 = x_86;
x_30 = x_73;
x_31 = x_76;
x_32 = x_71;
x_33 = x_117;
goto block_48;
}
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_1);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
