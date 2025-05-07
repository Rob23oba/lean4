// Lean compiler output
// Module: Lean.Compiler.IR.Format
// Imports: Lean.Compiler.IR.Basic
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringExpr;
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatFnBody_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody_loop(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_formatAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatIRType;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody___lam__0(lean_object*);
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatParam;
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatParams(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatFnBody_loop_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringDecl;
lean_object* l_Lean_formatKVMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatLitVal;
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatCtorInfo;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatArg;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody;
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatExpr;
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType;
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringExpr___lam__0(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_decl_to_string(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_mk_string_unchecked("x_", 2, 2);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("x_", 2, 2);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_mk_string_unchecked("◾", 3, 1);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
static lean_object* _init_l_Lean_IR_instToFormatArg() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_mk_string_unchecked(" ", 1, 1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_apply_1(x_1, x_3);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_nat_dec_lt(x_4, x_5);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_5, x_5);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_alloc_closure((void*)(l_Lean_IR_formatArray___redArg___lam__0), 3, 1);
lean_closure_set(x_18, 0, x_1);
x_19 = lean_usize_of_nat(x_4);
x_20 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_21 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_15, x_18, x_2, x_19, x_20, x_3);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_formatArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_String_quote(x_9);
lean_dec(x_9);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_String_quote(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_IR_instToFormatLitVal() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_31; uint8_t x_32; lean_object* x_46; uint8_t x_47; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_mk_string_unchecked("ctor_", 5, 5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_12);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_12);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_4);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = lean_nat_dec_lt(x_46, x_5);
x_32 = x_48;
goto block_45;
}
else
{
x_32 = x_47;
goto block_45;
}
block_30:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_name_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___lam__0___boxed), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_mk_string_unchecked("[", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unbox(x_18);
x_24 = l_Lean_Name_toString(x_2, x_23, x_17);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_mk_string_unchecked("]", 1, 1);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_dec(x_12);
lean_dec(x_2);
return x_13;
}
}
block_45:
{
if (x_32 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
x_13 = x_31;
goto block_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_12);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_mk_string_unchecked(".", 1, 1);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_12);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_12);
x_13 = x_44;
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instToFormatCtorInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_mk_string_unchecked(" ", 1, 1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(x_6);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(x_3);
x_6 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_4);
lean_dec(x_4);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(x_7);
x_10 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_mk_string_unchecked("reset[", 6, 6);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_16);
x_19 = lean_mk_string_unchecked("] ", 2, 2);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("x_", 2, 2);
x_23 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_29 = lean_mk_string_unchecked("reset[", 6, 6);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Init_Data_Repr_0__Nat_reprFast(x_27);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("] ", 2, 2);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("x_", 2, 2);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_28);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
case 2:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_mk_string_unchecked("reuse", 5, 5);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (x_44 == 0)
{
lean_object* x_67; 
x_67 = lean_mk_string_unchecked("", 0, 0);
x_48 = x_67;
goto block_66;
}
else
{
lean_object* x_68; 
x_68 = lean_mk_string_unchecked("!", 1, 1);
x_48 = x_68;
goto block_66;
}
block_66:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked(" ", 1, 1);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("x_", 2, 2);
x_55 = l___private_Init_Data_Repr_0__Nat_reprFast(x_42);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_mk_string_unchecked(" in ", 4, 4);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatCtorInfo(x_43);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_45);
lean_dec(x_45);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
case 3:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_1);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
x_72 = lean_mk_string_unchecked("proj[", 5, 5);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_75);
lean_ctor_set(x_1, 0, x_73);
x_76 = lean_mk_string_unchecked("] ", 2, 2);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("x_", 2, 2);
x_80 = l___private_Init_Data_Repr_0__Nat_reprFast(x_71);
x_81 = lean_string_append(x_79, x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_84 = lean_ctor_get(x_1, 0);
x_85 = lean_ctor_get(x_1, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_1);
x_86 = lean_mk_string_unchecked("proj[", 5, 5);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l___private_Init_Data_Repr_0__Nat_reprFast(x_84);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_mk_string_unchecked("] ", 2, 2);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked("x_", 2, 2);
x_95 = l___private_Init_Data_Repr_0__Nat_reprFast(x_85);
x_96 = lean_string_append(x_94, x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
case 4:
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_1);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_ctor_get(x_1, 0);
x_101 = lean_ctor_get(x_1, 1);
x_102 = lean_mk_string_unchecked("uproj[", 6, 6);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l___private_Init_Data_Repr_0__Nat_reprFast(x_100);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_103);
x_106 = lean_mk_string_unchecked("] ", 2, 2);
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("x_", 2, 2);
x_110 = l___private_Init_Data_Repr_0__Nat_reprFast(x_101);
x_111 = lean_string_append(x_109, x_110);
lean_dec(x_110);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_114 = lean_ctor_get(x_1, 0);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_1);
x_116 = lean_mk_string_unchecked("uproj[", 6, 6);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l___private_Init_Data_Repr_0__Nat_reprFast(x_114);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked("] ", 2, 2);
x_122 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_mk_string_unchecked("x_", 2, 2);
x_125 = l___private_Init_Data_Repr_0__Nat_reprFast(x_115);
x_126 = lean_string_append(x_124, x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
case 5:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_1, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_1, 2);
lean_inc(x_131);
lean_dec(x_1);
x_132 = lean_mk_string_unchecked("sproj[", 6, 6);
x_133 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l___private_Init_Data_Repr_0__Nat_reprFast(x_129);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked(", ", 2, 2);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = l___private_Init_Data_Repr_0__Nat_reprFast(x_130);
x_141 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked("] ", 2, 2);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_mk_string_unchecked("x_", 2, 2);
x_147 = l___private_Init_Data_Repr_0__Nat_reprFast(x_131);
x_148 = lean_string_append(x_146, x_147);
lean_dec(x_147);
x_149 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
case 6:
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_1);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_1, 0);
x_153 = lean_ctor_get(x_1, 1);
x_154 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_155 = lean_box(1);
x_156 = lean_unbox(x_155);
x_157 = l_Lean_Name_toString(x_152, x_156, x_154);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_153);
lean_dec(x_153);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_159);
lean_ctor_set(x_1, 0, x_158);
return x_1;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_160 = lean_ctor_get(x_1, 0);
x_161 = lean_ctor_get(x_1, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_1);
x_162 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_163 = lean_box(1);
x_164 = lean_unbox(x_163);
x_165 = l_Lean_Name_toString(x_160, x_164, x_162);
x_166 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_161);
lean_dec(x_161);
x_168 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
case 7:
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_1);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_170 = lean_ctor_get(x_1, 0);
x_171 = lean_ctor_get(x_1, 1);
x_172 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_173 = lean_mk_string_unchecked("pap ", 4, 4);
x_174 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_box(1);
x_176 = lean_unbox(x_175);
x_177 = l_Lean_Name_toString(x_170, x_176, x_172);
x_178 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_174);
x_179 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_171);
lean_dec(x_171);
x_180 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_180, 0, x_1);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_181 = lean_ctor_get(x_1, 0);
x_182 = lean_ctor_get(x_1, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_1);
x_183 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_184 = lean_mk_string_unchecked("pap ", 4, 4);
x_185 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_box(1);
x_187 = lean_unbox(x_186);
x_188 = l_Lean_Name_toString(x_181, x_187, x_183);
x_189 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_185);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_182);
lean_dec(x_182);
x_192 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
case 8:
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_1);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_194 = lean_ctor_get(x_1, 0);
x_195 = lean_ctor_get(x_1, 1);
x_196 = lean_mk_string_unchecked("app ", 4, 4);
x_197 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_mk_string_unchecked("x_", 2, 2);
x_199 = l___private_Init_Data_Repr_0__Nat_reprFast(x_194);
x_200 = lean_string_append(x_198, x_199);
lean_dec(x_199);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_201);
lean_ctor_set(x_1, 0, x_197);
x_202 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_195);
lean_dec(x_195);
x_203 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_204 = lean_ctor_get(x_1, 0);
x_205 = lean_ctor_get(x_1, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_1);
x_206 = lean_mk_string_unchecked("app ", 4, 4);
x_207 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_mk_string_unchecked("x_", 2, 2);
x_209 = l___private_Init_Data_Repr_0__Nat_reprFast(x_204);
x_210 = lean_string_append(x_208, x_209);
lean_dec(x_209);
x_211 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_205);
lean_dec(x_205);
x_214 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
case 9:
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_1);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_216 = lean_ctor_get(x_1, 1);
x_217 = lean_ctor_get(x_1, 0);
lean_dec(x_217);
x_218 = lean_mk_string_unchecked("box ", 4, 4);
x_219 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_mk_string_unchecked("x_", 2, 2);
x_221 = l___private_Init_Data_Repr_0__Nat_reprFast(x_216);
x_222 = lean_string_append(x_220, x_221);
lean_dec(x_221);
x_223 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_219);
return x_1;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_224 = lean_ctor_get(x_1, 1);
lean_inc(x_224);
lean_dec(x_1);
x_225 = lean_mk_string_unchecked("box ", 4, 4);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_mk_string_unchecked("x_", 2, 2);
x_228 = l___private_Init_Data_Repr_0__Nat_reprFast(x_224);
x_229 = lean_string_append(x_227, x_228);
lean_dec(x_228);
x_230 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_231 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_231, 0, x_226);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
case 10:
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_1);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_1, 0);
x_234 = lean_mk_string_unchecked("unbox ", 6, 6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_234);
x_235 = lean_mk_string_unchecked("x_", 2, 2);
x_236 = l___private_Init_Data_Repr_0__Nat_reprFast(x_233);
x_237 = lean_string_append(x_235, x_236);
lean_dec(x_236);
x_238 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_239, 0, x_1);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_1, 0);
lean_inc(x_240);
lean_dec(x_1);
x_241 = lean_mk_string_unchecked("unbox ", 6, 6);
x_242 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_243 = lean_mk_string_unchecked("x_", 2, 2);
x_244 = l___private_Init_Data_Repr_0__Nat_reprFast(x_240);
x_245 = lean_string_append(x_243, x_244);
lean_dec(x_244);
x_246 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_247, 0, x_242);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
case 11:
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_1, 0);
lean_inc(x_248);
lean_dec(x_1);
x_249 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatLitVal(x_248);
return x_249;
}
default: 
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_1);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_251 = lean_ctor_get(x_1, 0);
x_252 = lean_mk_string_unchecked("isShared ", 9, 9);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_252);
x_253 = lean_mk_string_unchecked("x_", 2, 2);
x_254 = l___private_Init_Data_Repr_0__Nat_reprFast(x_251);
x_255 = lean_string_append(x_253, x_254);
lean_dec(x_254);
x_256 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_257, 0, x_1);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_258 = lean_ctor_get(x_1, 0);
lean_inc(x_258);
lean_dec(x_1);
x_259 = lean_mk_string_unchecked("isShared ", 9, 9);
x_260 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_mk_string_unchecked("x_", 2, 2);
x_262 = l___private_Init_Data_Repr_0__Nat_reprFast(x_258);
x_263 = lean_string_append(x_261, x_262);
lean_dec(x_262);
x_264 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_265 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_265, 0, x_260);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instToFormatExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(x_1);
x_3 = lean_unsigned_to_nat(120u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_2, x_3, x_4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instToStringExpr() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToStringExpr___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_10);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_7);
x_9 = l_List_foldl___at___Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0_spec__0(x_2, x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("float", 5, 5);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_string_unchecked("u8", 2, 2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_string_unchecked("u16", 3, 3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_mk_string_unchecked("u32", 3, 3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_mk_string_unchecked("u64", 3, 3);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_mk_string_unchecked("usize", 5, 5);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_mk_string_unchecked("◾", 3, 1);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_mk_string_unchecked("obj", 3, 3);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 8:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_mk_string_unchecked("tobj", 4, 4);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 9:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_mk_string_unchecked("float32", 7, 7);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
case 10:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_mk_string_unchecked("struct ", 7, 7);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_mk_string_unchecked("{", 1, 1);
x_28 = lean_array_to_list(x_23);
x_29 = lean_mk_string_unchecked(", ", 2, 2);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(x_28, x_30);
x_32 = lean_mk_string_unchecked("}", 1, 1);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_to_int(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_31);
lean_ctor_set(x_1, 0, x_35);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_32);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_41);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_mk_string_unchecked("struct ", 7, 7);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_mk_string_unchecked("{", 1, 1);
x_47 = lean_array_to_list(x_43);
x_48 = lean_mk_string_unchecked(", ", 2, 2);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(x_47, x_49);
x_51 = lean_mk_string_unchecked("}", 1, 1);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_to_int(x_52);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_46);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_unbox(x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_61);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
default: 
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_1);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_64 = lean_ctor_get(x_1, 1);
x_65 = lean_ctor_get(x_1, 0);
lean_dec(x_65);
x_66 = lean_mk_string_unchecked("union ", 6, 6);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_mk_string_unchecked("{", 1, 1);
x_69 = lean_array_to_list(x_64);
x_70 = lean_mk_string_unchecked(", ", 2, 2);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(x_69, x_71);
x_73 = lean_mk_string_unchecked("}", 1, 1);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_to_int(x_74);
x_76 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_72);
lean_ctor_set(x_1, 0, x_76);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_73);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_81, 0, x_79);
x_82 = lean_unbox(x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_82);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_67);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_84 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
lean_dec(x_1);
x_85 = lean_mk_string_unchecked("union ", 6, 6);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_mk_string_unchecked("{", 1, 1);
x_88 = lean_array_to_list(x_84);
x_89 = lean_mk_string_unchecked(", ", 2, 2);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Std_Format_joinSep___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType_spec__0(x_88, x_90);
x_92 = lean_mk_string_unchecked("}", 1, 1);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_to_int(x_93);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_87);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_101, 0, x_99);
x_102 = lean_unbox(x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_102);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_86);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_instToFormatIRType() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringIRType___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(120u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_format_pretty(x_1, x_2, x_3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instToStringIRType() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToStringIRType___lam__0), 1, 0);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, lean_box(0));
lean_closure_set(x_3, 3, x_1);
lean_closure_set(x_3, 4, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("(", 1, 1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_mk_string_unchecked("x_", 2, 2);
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked(" : ", 3, 3);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
if (x_3 == 0)
{
lean_object* x_24; 
x_24 = lean_mk_string_unchecked("", 0, 0);
x_15 = x_24;
goto block_23;
}
else
{
lean_object* x_25; 
x_25 = lean_mk_string_unchecked("@& ", 3, 3);
x_15 = x_25;
goto block_23;
}
block_23:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_4);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked(")", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
static lean_object* _init_l_Lean_IR_instToFormatParam() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_8, x_10, x_7);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_mk_string_unchecked(" →", 4, 2);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_12);
x_15 = lean_nat_to_int(x_2);
x_16 = lean_box(1);
x_17 = lean_apply_1(x_1, x_6);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_Name_toString(x_24, x_26, x_23);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_mk_string_unchecked(" →", 4, 2);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_nat_to_int(x_2);
x_33 = lean_box(1);
x_34 = lean_apply_1(x_1, x_22);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_3);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_mk_string_unchecked("default →", 11, 9);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_40);
x_41 = lean_nat_to_int(x_2);
x_42 = lean_box(1);
x_43 = lean_apply_1(x_1, x_39);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_mk_string_unchecked("default →", 11, 9);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_nat_to_int(x_2);
x_51 = lean_box(1);
x_52 = lean_apply_1(x_1, x_47);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_mk_string_unchecked(" ", 1, 1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatParam(x_6);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBodyHead(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("let ", 4, 4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_mk_string_unchecked("x_", 2, 2);
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked(" : ", 3, 3);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_3);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(" := ", 4, 4);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(x_4);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("block_", 6, 6);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_23);
lean_dec(x_23);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked(" := ...", 7, 7);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("set ", 4, 4);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_mk_string_unchecked("x_", 2, 2);
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("[", 1, 1);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Init_Data_Repr_0__Nat_reprFast(x_34);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked("] := ", 5, 5);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(x_35);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
case 3:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_mk_string_unchecked("setTag ", 7, 7);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_mk_string_unchecked("x_", 2, 2);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_54);
x_60 = lean_string_append(x_58, x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_mk_string_unchecked(" := ", 4, 4);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
case 4:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
lean_dec(x_1);
x_72 = lean_mk_string_unchecked("uset ", 5, 5);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_mk_string_unchecked("x_", 2, 2);
x_75 = l___private_Init_Data_Repr_0__Nat_reprFast(x_69);
lean_inc(x_74);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("[", 1, 1);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_83 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("] := ", 5, 5);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l___private_Init_Data_Repr_0__Nat_reprFast(x_71);
x_89 = lean_string_append(x_74, x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
case 5:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 4);
lean_inc(x_96);
lean_dec(x_1);
x_97 = lean_mk_string_unchecked("sset ", 5, 5);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_mk_string_unchecked("x_", 2, 2);
x_100 = l___private_Init_Data_Repr_0__Nat_reprFast(x_92);
lean_inc(x_99);
x_101 = lean_string_append(x_99, x_100);
lean_dec(x_100);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked("[", 1, 1);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Init_Data_Repr_0__Nat_reprFast(x_93);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_mk_string_unchecked(", ", 2, 2);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Init_Data_Repr_0__Nat_reprFast(x_94);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("] : ", 4, 4);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_96);
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_mk_string_unchecked(" := ", 4, 4);
x_122 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = l___private_Init_Data_Repr_0__Nat_reprFast(x_95);
x_125 = lean_string_append(x_99, x_124);
lean_dec(x_124);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
case 6:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_143; uint8_t x_144; 
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_1, 1);
lean_inc(x_129);
lean_dec(x_1);
x_130 = lean_mk_string_unchecked("inc", 3, 3);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_dec_eq(x_129, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_145 = l___private_Init_Data_Repr_0__Nat_reprFast(x_129);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_mk_string_unchecked("[", 1, 1);
x_148 = lean_mk_string_unchecked("]", 1, 1);
x_149 = lean_nat_to_int(x_143);
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_147);
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_148);
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_156, 0, x_154);
x_157 = lean_unbox(x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_157);
x_132 = x_156;
goto block_142;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_129);
x_158 = lean_mk_string_unchecked("", 0, 0);
x_159 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_132 = x_159;
goto block_142;
}
block_142:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked(" ", 1, 1);
x_135 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked("x_", 2, 2);
x_138 = l___private_Init_Data_Repr_0__Nat_reprFast(x_128);
x_139 = lean_string_append(x_137, x_138);
lean_dec(x_138);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
case 7:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_175; uint8_t x_176; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 1);
lean_inc(x_161);
lean_dec(x_1);
x_162 = lean_mk_string_unchecked("dec", 3, 3);
x_163 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_dec_eq(x_161, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_177 = l___private_Init_Data_Repr_0__Nat_reprFast(x_161);
x_178 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_mk_string_unchecked("[", 1, 1);
x_180 = lean_mk_string_unchecked("]", 1, 1);
x_181 = lean_nat_to_int(x_175);
x_182 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_182, 0, x_179);
x_183 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_178);
x_184 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_184, 0, x_180);
x_185 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_188, 0, x_186);
x_189 = lean_unbox(x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*1, x_189);
x_164 = x_188;
goto block_174;
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_161);
x_190 = lean_mk_string_unchecked("", 0, 0);
x_191 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_164 = x_191;
goto block_174;
}
block_174:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_mk_string_unchecked(" ", 1, 1);
x_167 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_mk_string_unchecked("x_", 2, 2);
x_170 = l___private_Init_Data_Repr_0__Nat_reprFast(x_160);
x_171 = lean_string_append(x_169, x_170);
lean_dec(x_170);
x_172 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
case 8:
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_1);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_193 = lean_ctor_get(x_1, 0);
x_194 = lean_ctor_get(x_1, 1);
lean_dec(x_194);
x_195 = lean_mk_string_unchecked("del ", 4, 4);
x_196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = lean_mk_string_unchecked("x_", 2, 2);
x_198 = l___private_Init_Data_Repr_0__Nat_reprFast(x_193);
x_199 = lean_string_append(x_197, x_198);
lean_dec(x_198);
x_200 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_200);
lean_ctor_set(x_1, 0, x_196);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_1, 0);
lean_inc(x_201);
lean_dec(x_1);
x_202 = lean_mk_string_unchecked("del ", 4, 4);
x_203 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_mk_string_unchecked("x_", 2, 2);
x_205 = l___private_Init_Data_Repr_0__Nat_reprFast(x_201);
x_206 = lean_string_append(x_204, x_205);
lean_dec(x_205);
x_207 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_208, 0, x_203);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
case 9:
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_1);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_1, 0);
x_211 = lean_ctor_get(x_1, 1);
lean_dec(x_211);
x_212 = lean_mk_string_unchecked("mdata ", 6, 6);
x_213 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = l_Lean_formatKVMap(x_210);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_214);
lean_ctor_set(x_1, 0, x_213);
return x_1;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_1, 0);
lean_inc(x_215);
lean_dec(x_1);
x_216 = lean_mk_string_unchecked("mdata ", 6, 6);
x_217 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_217, 0, x_216);
x_218 = l_Lean_formatKVMap(x_215);
x_219 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
case 10:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_220 = lean_ctor_get(x_1, 1);
lean_inc(x_220);
lean_dec(x_1);
x_221 = lean_mk_string_unchecked("case ", 5, 5);
x_222 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_mk_string_unchecked("x_", 2, 2);
x_224 = l___private_Init_Data_Repr_0__Nat_reprFast(x_220);
x_225 = lean_string_append(x_223, x_224);
lean_dec(x_224);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_227, 0, x_222);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_mk_string_unchecked(" of ...", 7, 7);
x_229 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
case 11:
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_1);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_1, 0);
x_233 = lean_mk_string_unchecked("ret ", 4, 4);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_233);
x_234 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(x_232);
x_235 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_235, 0, x_1);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_1, 0);
lean_inc(x_236);
lean_dec(x_1);
x_237 = lean_mk_string_unchecked("ret ", 4, 4);
x_238 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(x_236);
x_240 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
case 12:
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_1);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_242 = lean_ctor_get(x_1, 0);
x_243 = lean_ctor_get(x_1, 1);
x_244 = lean_mk_string_unchecked("jmp ", 4, 4);
x_245 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_246 = lean_mk_string_unchecked("block_", 6, 6);
x_247 = l___private_Init_Data_Repr_0__Nat_reprFast(x_242);
x_248 = lean_string_append(x_246, x_247);
lean_dec(x_247);
x_249 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_249);
lean_ctor_set(x_1, 0, x_245);
x_250 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_243);
lean_dec(x_243);
x_251 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_251, 0, x_1);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_252 = lean_ctor_get(x_1, 0);
x_253 = lean_ctor_get(x_1, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_1);
x_254 = lean_mk_string_unchecked("jmp ", 4, 4);
x_255 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_255, 0, x_254);
x_256 = lean_mk_string_unchecked("block_", 6, 6);
x_257 = l___private_Init_Data_Repr_0__Nat_reprFast(x_252);
x_258 = lean_string_append(x_256, x_257);
lean_dec(x_257);
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_260, 0, x_255);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_253);
lean_dec(x_253);
x_262 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
default: 
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_mk_string_unchecked("⊥", 3, 1);
x_264 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
}
}
}
LEAN_EXPORT lean_object* lean_ir_format_fn_body_head(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_formatFnBodyHead(x_1);
x_3 = lean_unsigned_to_nat(120u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_format_pretty(x_2, x_3, x_4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatFnBody_loop_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_IR_formatFnBody_loop), 2, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_1);
x_11 = l_Lean_IR_formatAlt(x_10, x_1, x_7);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_mk_string_unchecked("let ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("x_", 2, 2);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(" : ", 3, 3);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_4);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(" := ", 4, 4);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr(x_5);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked(";", 1, 1);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_IR_formatFnBody_loop(x_1, x_6);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 3);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_mk_string_unchecked("block_", 6, 6);
x_36 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_32);
lean_dec(x_32);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked(" :=", 3, 3);
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_1);
x_44 = lean_nat_to_int(x_1);
x_45 = lean_box(1);
lean_inc(x_1);
x_46 = l_Lean_IR_formatFnBody_loop(x_1, x_33);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked(";", 1, 1);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
x_54 = l_Lean_IR_formatFnBody_loop(x_1, x_34);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 3);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_mk_string_unchecked("set ", 4, 4);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_mk_string_unchecked("x_", 2, 2);
x_63 = l___private_Init_Data_Repr_0__Nat_reprFast(x_56);
x_64 = lean_string_append(x_62, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_mk_string_unchecked("[", 1, 1);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Init_Data_Repr_0__Nat_reprFast(x_57);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_mk_string_unchecked("] := ", 5, 5);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(x_58);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked(";", 1, 1);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_box(1);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_IR_formatFnBody_loop(x_1, x_59);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
case 3:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
lean_dec(x_2);
x_88 = lean_mk_string_unchecked("setTag ", 7, 7);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_mk_string_unchecked("x_", 2, 2);
x_91 = l___private_Init_Data_Repr_0__Nat_reprFast(x_85);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_mk_string_unchecked(" := ", 4, 4);
x_96 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = l___private_Init_Data_Repr_0__Nat_reprFast(x_86);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_mk_string_unchecked(";", 1, 1);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_box(1);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_IR_formatFnBody_loop(x_1, x_87);
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
case 4:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_108 = lean_ctor_get(x_2, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_2, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_2, 3);
lean_inc(x_111);
lean_dec(x_2);
x_112 = lean_mk_string_unchecked("uset ", 5, 5);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_mk_string_unchecked("x_", 2, 2);
x_115 = l___private_Init_Data_Repr_0__Nat_reprFast(x_108);
lean_inc(x_114);
x_116 = lean_string_append(x_114, x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_mk_string_unchecked("[", 1, 1);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_122 = l___private_Init_Data_Repr_0__Nat_reprFast(x_109);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_mk_string_unchecked("] := ", 5, 5);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_Init_Data_Repr_0__Nat_reprFast(x_110);
x_129 = lean_string_append(x_114, x_128);
lean_dec(x_128);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_mk_string_unchecked(";", 1, 1);
x_133 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_box(1);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_IR_formatFnBody_loop(x_1, x_111);
x_138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
case 5:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_139 = lean_ctor_get(x_2, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_2, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_2, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_2, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_2, 5);
lean_inc(x_144);
lean_dec(x_2);
x_145 = lean_mk_string_unchecked("sset ", 5, 5);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_mk_string_unchecked("x_", 2, 2);
x_148 = l___private_Init_Data_Repr_0__Nat_reprFast(x_139);
lean_inc(x_147);
x_149 = lean_string_append(x_147, x_148);
lean_dec(x_148);
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_mk_string_unchecked("[", 1, 1);
x_153 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
x_155 = l___private_Init_Data_Repr_0__Nat_reprFast(x_140);
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_mk_string_unchecked(", ", 2, 2);
x_159 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
x_161 = l___private_Init_Data_Repr_0__Nat_reprFast(x_141);
x_162 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_mk_string_unchecked("] : ", 4, 4);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_143);
x_168 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_mk_string_unchecked(" := ", 4, 4);
x_170 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_170);
x_172 = l___private_Init_Data_Repr_0__Nat_reprFast(x_142);
x_173 = lean_string_append(x_147, x_172);
lean_dec(x_172);
x_174 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_mk_string_unchecked(";", 1, 1);
x_177 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_box(1);
x_180 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_IR_formatFnBody_loop(x_1, x_144);
x_182 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
case 6:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_206; uint8_t x_207; 
x_183 = lean_ctor_get(x_2, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_2, 2);
lean_inc(x_185);
lean_dec(x_2);
x_186 = lean_mk_string_unchecked("inc", 3, 3);
x_187 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_187, 0, x_186);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_dec_eq(x_184, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_208 = l___private_Init_Data_Repr_0__Nat_reprFast(x_184);
x_209 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_209, 0, x_208);
x_210 = lean_mk_string_unchecked("[", 1, 1);
x_211 = lean_mk_string_unchecked("]", 1, 1);
x_212 = lean_nat_to_int(x_206);
x_213 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_213, 0, x_210);
x_214 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_209);
x_215 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_215, 0, x_211);
x_216 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_219, 0, x_217);
x_220 = lean_unbox(x_218);
lean_ctor_set_uint8(x_219, sizeof(void*)*1, x_220);
x_188 = x_219;
goto block_205;
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_184);
x_221 = lean_mk_string_unchecked("", 0, 0);
x_222 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_188 = x_222;
goto block_205;
}
block_205:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_189 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_mk_string_unchecked(" ", 1, 1);
x_191 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_mk_string_unchecked("x_", 2, 2);
x_194 = l___private_Init_Data_Repr_0__Nat_reprFast(x_183);
x_195 = lean_string_append(x_193, x_194);
lean_dec(x_194);
x_196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_mk_string_unchecked(";", 1, 1);
x_199 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_box(1);
x_202 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_IR_formatFnBody_loop(x_1, x_185);
x_204 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
case 7:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_246; uint8_t x_247; 
x_223 = lean_ctor_get(x_2, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_2, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_2, 2);
lean_inc(x_225);
lean_dec(x_2);
x_226 = lean_mk_string_unchecked("dec", 3, 3);
x_227 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_dec_eq(x_224, x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_248 = l___private_Init_Data_Repr_0__Nat_reprFast(x_224);
x_249 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_250 = lean_mk_string_unchecked("[", 1, 1);
x_251 = lean_mk_string_unchecked("]", 1, 1);
x_252 = lean_nat_to_int(x_246);
x_253 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_253, 0, x_250);
x_254 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_249);
x_255 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_255, 0, x_251);
x_256 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_box(0);
x_259 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_259, 0, x_257);
x_260 = lean_unbox(x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_260);
x_228 = x_259;
goto block_245;
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_224);
x_261 = lean_mk_string_unchecked("", 0, 0);
x_262 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_262, 0, x_261);
x_228 = x_262;
goto block_245;
}
block_245:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_229 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_mk_string_unchecked(" ", 1, 1);
x_231 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_mk_string_unchecked("x_", 2, 2);
x_234 = l___private_Init_Data_Repr_0__Nat_reprFast(x_223);
x_235 = lean_string_append(x_233, x_234);
lean_dec(x_234);
x_236 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_237, 0, x_232);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_mk_string_unchecked(";", 1, 1);
x_239 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_box(1);
x_242 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_IR_formatFnBody_loop(x_1, x_225);
x_244 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
case 8:
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_2);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_264 = lean_ctor_get(x_2, 0);
x_265 = lean_ctor_get(x_2, 1);
x_266 = lean_mk_string_unchecked("del ", 4, 4);
x_267 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = lean_mk_string_unchecked("x_", 2, 2);
x_269 = l___private_Init_Data_Repr_0__Nat_reprFast(x_264);
x_270 = lean_string_append(x_268, x_269);
lean_dec(x_269);
x_271 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_271);
lean_ctor_set(x_2, 0, x_267);
x_272 = lean_mk_string_unchecked(";", 1, 1);
x_273 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_274 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_274, 0, x_2);
lean_ctor_set(x_274, 1, x_273);
x_275 = lean_box(1);
x_276 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_IR_formatFnBody_loop(x_1, x_265);
x_278 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_279 = lean_ctor_get(x_2, 0);
x_280 = lean_ctor_get(x_2, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_2);
x_281 = lean_mk_string_unchecked("del ", 4, 4);
x_282 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_282, 0, x_281);
x_283 = lean_mk_string_unchecked("x_", 2, 2);
x_284 = l___private_Init_Data_Repr_0__Nat_reprFast(x_279);
x_285 = lean_string_append(x_283, x_284);
lean_dec(x_284);
x_286 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_287 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_287, 0, x_282);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_mk_string_unchecked(";", 1, 1);
x_289 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_290 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_box(1);
x_292 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Lean_IR_formatFnBody_loop(x_1, x_280);
x_294 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
case 9:
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_2);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_296 = lean_ctor_get(x_2, 0);
x_297 = lean_ctor_get(x_2, 1);
x_298 = lean_mk_string_unchecked("mdata ", 6, 6);
x_299 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_299, 0, x_298);
x_300 = l_Lean_formatKVMap(x_296);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_300);
lean_ctor_set(x_2, 0, x_299);
x_301 = lean_mk_string_unchecked(";", 1, 1);
x_302 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_303 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_303, 0, x_2);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_box(1);
x_305 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_IR_formatFnBody_loop(x_1, x_297);
x_307 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_308 = lean_ctor_get(x_2, 0);
x_309 = lean_ctor_get(x_2, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_2);
x_310 = lean_mk_string_unchecked("mdata ", 6, 6);
x_311 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_311, 0, x_310);
x_312 = l_Lean_formatKVMap(x_308);
x_313 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_mk_string_unchecked(";", 1, 1);
x_315 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_315, 0, x_314);
x_316 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_box(1);
x_318 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_IR_formatFnBody_loop(x_1, x_309);
x_320 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
case 10:
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_321 = lean_ctor_get(x_2, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_2, 2);
lean_inc(x_322);
x_323 = lean_ctor_get(x_2, 3);
lean_inc(x_323);
lean_dec(x_2);
x_324 = lean_mk_string_unchecked("case ", 5, 5);
x_325 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = lean_mk_string_unchecked("x_", 2, 2);
x_327 = l___private_Init_Data_Repr_0__Nat_reprFast(x_321);
x_328 = lean_string_append(x_326, x_327);
lean_dec(x_327);
x_329 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_329, 0, x_328);
x_330 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_mk_string_unchecked(" : ", 3, 3);
x_332 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_332);
x_334 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_322);
x_335 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_mk_string_unchecked(" of", 3, 3);
x_337 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_337, 0, x_336);
x_338 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_box(0);
x_340 = lean_unsigned_to_nat(0u);
x_341 = lean_array_get_size(x_323);
x_342 = lean_nat_dec_lt(x_340, x_341);
if (x_342 == 0)
{
lean_object* x_343; 
lean_dec(x_341);
lean_dec(x_323);
lean_dec(x_1);
x_343 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_339);
return x_343;
}
else
{
uint8_t x_344; 
x_344 = lean_nat_dec_le(x_341, x_341);
if (x_344 == 0)
{
lean_object* x_345; 
lean_dec(x_341);
lean_dec(x_323);
lean_dec(x_1);
x_345 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_345, 1, x_339);
return x_345;
}
else
{
size_t x_346; size_t x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_usize_of_nat(x_340);
x_347 = lean_usize_of_nat(x_341);
lean_dec(x_341);
x_348 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatFnBody_loop_spec__0(x_1, x_323, x_346, x_347, x_339);
lean_dec(x_323);
x_349 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_349, 0, x_338);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
case 11:
{
uint8_t x_350; 
lean_dec(x_1);
x_350 = !lean_is_exclusive(x_2);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_2, 0);
x_352 = lean_mk_string_unchecked("ret ", 4, 4);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_352);
x_353 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(x_351);
x_354 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_354, 0, x_2);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_355 = lean_ctor_get(x_2, 0);
lean_inc(x_355);
lean_dec(x_2);
x_356 = lean_mk_string_unchecked("ret ", 4, 4);
x_357 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_357, 0, x_356);
x_358 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatArg(x_355);
x_359 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
case 12:
{
uint8_t x_360; 
lean_dec(x_1);
x_360 = !lean_is_exclusive(x_2);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_361 = lean_ctor_get(x_2, 0);
x_362 = lean_ctor_get(x_2, 1);
x_363 = lean_mk_string_unchecked("jmp ", 4, 4);
x_364 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_364, 0, x_363);
x_365 = lean_mk_string_unchecked("block_", 6, 6);
x_366 = l___private_Init_Data_Repr_0__Nat_reprFast(x_361);
x_367 = lean_string_append(x_365, x_366);
lean_dec(x_366);
x_368 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_368);
lean_ctor_set(x_2, 0, x_364);
x_369 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_362);
lean_dec(x_362);
x_370 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_370, 0, x_2);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_371 = lean_ctor_get(x_2, 0);
x_372 = lean_ctor_get(x_2, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_2);
x_373 = lean_mk_string_unchecked("jmp ", 4, 4);
x_374 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_374, 0, x_373);
x_375 = lean_mk_string_unchecked("block_", 6, 6);
x_376 = l___private_Init_Data_Repr_0__Nat_reprFast(x_371);
x_377 = lean_string_append(x_375, x_376);
lean_dec(x_376);
x_378 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_378, 0, x_377);
x_379 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_379, 0, x_374);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_Lean_IR_formatArray___at_____private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr_spec__0(x_372);
lean_dec(x_372);
x_381 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
default: 
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_1);
x_382 = lean_mk_string_unchecked("⊥", 3, 1);
x_383 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_formatFnBody_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_formatFnBody_loop_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_formatFnBody_loop(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatFnBody___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatFnBody_loop(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instToFormatFnBody() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToFormatFnBody___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringFnBody___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatFnBody_loop(x_2, x_1);
x_4 = lean_unsigned_to_nat(120u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_format_pretty(x_3, x_4, x_5, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_instToStringFnBody() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToStringFnBody___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_formatDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_8 = lean_mk_string_unchecked("def ", 4, 4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_3, x_11, x_7);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked(" : ", 3, 3);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_5);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked(" :=", 3, 3);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_2);
x_25 = lean_nat_to_int(x_2);
x_26 = lean_box(1);
x_27 = l_Lean_IR_formatFnBody_loop(x_2, x_6);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatExpr___lam__0___boxed), 1, 0);
x_35 = lean_mk_string_unchecked("extern ", 7, 7);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Name_toString(x_31, x_38, x_34);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_IR_formatArray___at___Lean_IR_formatParams_spec__0(x_32);
lean_dec(x_32);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked(" : ", 3, 3);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_33);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatDecl___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatDecl(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instToFormatDecl() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToFormatDecl___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_ir_decl_to_string(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatDecl(x_1, x_2);
x_4 = lean_unsigned_to_nat(120u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_format_pretty(x_3, x_4, x_5, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_instToStringDecl() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_ir_decl_to_string), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_instToFormatArg = _init_l_Lean_IR_instToFormatArg();
lean_mark_persistent(l_Lean_IR_instToFormatArg);
l_Lean_IR_instToFormatLitVal = _init_l_Lean_IR_instToFormatLitVal();
lean_mark_persistent(l_Lean_IR_instToFormatLitVal);
l_Lean_IR_instToFormatCtorInfo = _init_l_Lean_IR_instToFormatCtorInfo();
lean_mark_persistent(l_Lean_IR_instToFormatCtorInfo);
l_Lean_IR_instToFormatExpr = _init_l_Lean_IR_instToFormatExpr();
lean_mark_persistent(l_Lean_IR_instToFormatExpr);
l_Lean_IR_instToStringExpr = _init_l_Lean_IR_instToStringExpr();
lean_mark_persistent(l_Lean_IR_instToStringExpr);
l_Lean_IR_instToFormatIRType = _init_l_Lean_IR_instToFormatIRType();
lean_mark_persistent(l_Lean_IR_instToFormatIRType);
l_Lean_IR_instToStringIRType = _init_l_Lean_IR_instToStringIRType();
lean_mark_persistent(l_Lean_IR_instToStringIRType);
l_Lean_IR_instToFormatParam = _init_l_Lean_IR_instToFormatParam();
lean_mark_persistent(l_Lean_IR_instToFormatParam);
l_Lean_IR_instToFormatFnBody = _init_l_Lean_IR_instToFormatFnBody();
lean_mark_persistent(l_Lean_IR_instToFormatFnBody);
l_Lean_IR_instToStringFnBody = _init_l_Lean_IR_instToStringFnBody();
lean_mark_persistent(l_Lean_IR_instToStringFnBody);
l_Lean_IR_instToFormatDecl = _init_l_Lean_IR_instToFormatDecl();
lean_mark_persistent(l_Lean_IR_instToFormatDecl);
l_Lean_IR_instToStringDecl = _init_l_Lean_IR_instToStringDecl();
lean_mark_persistent(l_Lean_IR_instToStringDecl);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
