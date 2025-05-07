// Lean compiler output
// Module: Lake.Util.Proc
// Imports: Lake.Util.Log
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__1(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object*);
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_testProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_mk_string_unchecked("PATH", 4, 4);
x_14 = lean_string_dec_eq(x_11, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_mk_string_unchecked("=", 1, 1);
x_16 = lean_string_append(x_11, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_22; 
x_22 = lean_mk_string_unchecked("", 0, 0);
x_17 = x_22;
goto block_21;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_17 = x_23;
goto block_21;
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked(" ", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_7 = x_20;
goto block_10;
}
}
else
{
lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
x_24 = lean_mk_string_unchecked("PATH ", 5, 5);
x_7 = x_24;
goto block_10;
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkCmdLog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_3 = lean_array_to_list(x_2);
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at___Lake_mkCmdLog_spec__0(x_3, x_4);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = l_List_foldl___at___Lake_mkCmdLog_spec__1(x_6, x_5);
lean_dec(x_5);
x_8 = lean_mk_string_unchecked(" ", 1, 1);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_array_to_list(x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_String_intercalate(x_8, x_12);
lean_dec(x_8);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_mk_string_unchecked(".", 1, 1);
x_14 = x_21;
goto block_19;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_14 = x_22;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_mk_string_unchecked("> ", 2, 2);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_7);
lean_dec(x_7);
x_18 = lean_string_append(x_17, x_13);
lean_dec(x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_mkCmdLog_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___Lake_mkCmdLog_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_instDecidableEqPos(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_9 = lean_mk_string_unchecked("stderr:\n", 8, 8);
x_10 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
lean_inc(x_10);
x_11 = l_Substring_takeWhileAux(x_5, x_6, x_10, x_7);
x_12 = l_Substring_takeRightWhileAux(x_5, x_11, x_10, x_6);
x_13 = lean_string_utf8_extract(x_5, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = lean_string_append(x_9, x_13);
lean_dec(x_13);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_instDecidableEqPos(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("stdout:\n", 8, 8);
x_12 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
lean_inc(x_12);
x_13 = l_Substring_takeWhileAux(x_5, x_6, x_12, x_7);
x_14 = l_Substring_takeRightWhileAux(x_5, x_13, x_12, x_6);
x_15 = lean_string_utf8_extract(x_5, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_16 = lean_string_append(x_11, x_15);
lean_dec(x_15);
x_17 = lean_apply_1(x_3, x_16);
x_18 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_17, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_19, 0, x_4);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_24, x_19);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_instDecidableEqPos(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_5);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_mk_string_unchecked("stdout:\n", 8, 8);
x_13 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
lean_inc(x_13);
x_14 = l_Substring_takeWhileAux(x_6, x_7, x_13, x_8);
x_15 = l_Substring_takeRightWhileAux(x_6, x_14, x_13, x_7);
x_16 = lean_string_utf8_extract(x_6, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = lean_apply_1(x_4, x_17);
x_19 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_18, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_20 = lean_alloc_closure((void*)(l_Lake_logOutput___redArg___lam__1), 2, 1);
lean_closure_set(x_20, 0, x_5);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_25, x_20);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_logOutput___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_logOutput___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_Process_output(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_mk_string_unchecked("failed to execute '", 19, 19);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_mk_string_unchecked("': ", 3, 3);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = lean_io_error_to_string(x_14);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_box(3);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = lean_array_get_size(x_3);
x_26 = lean_array_push(x_3, x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_30 = lean_mk_string_unchecked("failed to execute '", 19, 19);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_mk_string_unchecked("': ", 3, 3);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_io_error_to_string(x_28);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_box(3);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_array_get_size(x_3);
x_41 = lean_array_push(x_3, x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_29);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_20; 
x_20 = lean_array_get_size(x_3);
if (x_2 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_1);
x_21 = l_Lake_mkCmdLog(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = lean_box(0);
x_26 = lean_array_push(x_3, x_23);
x_27 = l_Lake_rawProc___lam__0(x_1, x_25, x_26, x_4);
lean_dec(x_1);
x_5 = x_20;
x_6 = x_27;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lake_rawProc___lam__0(x_1, x_28, x_3, x_4);
lean_dec(x_1);
x_5 = x_20;
x_6 = x_29;
goto block_19;
}
block_19:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_7);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_5);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_16 = x_7;
} else {
 lean_dec_ref(x_7);
 x_16 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(1, 2, 0);
} else {
 x_17 = x_16;
}
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_rawProc___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_rawProc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_rawProc(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = lean_box(0);
x_10 = lean_array_push(x_4, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_2);
x_14 = lean_box(0);
x_15 = lean_array_push(x_4, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_string_utf8_byte_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_instDecidableEqPos(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_mk_string_unchecked("stderr:\n", 8, 8);
x_11 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_6, x_7, x_8);
x_12 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_6, x_11, x_7);
x_13 = lean_string_utf8_extract(x_6, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = lean_string_append(x_10, x_13);
lean_dec(x_13);
x_15 = lean_apply_3(x_2, x_14, x_4, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_array_get_size(x_3);
lean_inc(x_1);
x_11 = l_Lake_mkCmdLog(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = l_IO_Process_output(x_1, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_90 = lean_array_push(x_3, x_13);
x_91 = lean_box(x_2);
x_92 = lean_alloc_closure((void*)(l_Lake_proc___lam__0___boxed), 5, 2);
lean_closure_set(x_92, 0, x_91);
lean_closure_set(x_92, 1, x_12);
x_93 = lean_ctor_get(x_16, 0);
lean_inc(x_93);
x_94 = lean_string_utf8_byte_size(x_93);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l_instDecidableEqPos(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_97 = lean_mk_string_unchecked("stdout:\n", 8, 8);
x_98 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_93, x_94, x_95);
x_99 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_93, x_98, x_94);
x_100 = lean_string_utf8_extract(x_93, x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_93);
x_101 = lean_string_append(x_97, x_100);
lean_dec(x_100);
x_102 = lean_unbox(x_12);
x_103 = l_Lake_proc___lam__0(x_2, x_102, x_101, x_90, x_17);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = l_Lake_proc___lam__1(x_16, x_92, x_106, x_107, x_105);
lean_dec(x_106);
x_18 = x_108;
goto block_89;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_94);
lean_dec(x_93);
x_109 = lean_box(0);
x_110 = l_Lake_proc___lam__1(x_16, x_92, x_109, x_90, x_17);
x_18 = x_110;
goto block_89;
}
block_89:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; uint32_t x_28; uint8_t x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = lean_ctor_get_uint32(x_16, sizeof(void*)*2);
lean_dec(x_16);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_uint32_of_nat(x_27);
x_29 = lean_uint32_dec_eq(x_26, x_28);
x_30 = l_instDecidableNot___redArg(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_19, 0, x_31);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
lean_free_object(x_19);
lean_free_object(x_18);
x_32 = lean_mk_string_unchecked("external command '", 18, 18);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_mk_string_unchecked("' exited with code ", 19, 19);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = lean_uint32_to_nat(x_26);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_37);
x_39 = lean_string_append(x_36, x_38);
lean_dec(x_38);
x_40 = lean_box(3);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_unbox(x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
x_43 = lean_array_push(x_24, x_41);
x_6 = x_43;
x_7 = x_21;
goto block_10;
}
}
else
{
lean_object* x_44; uint32_t x_45; lean_object* x_46; uint32_t x_47; uint8_t x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_dec(x_19);
x_45 = lean_ctor_get_uint32(x_16, sizeof(void*)*2);
lean_dec(x_16);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_uint32_of_nat(x_46);
x_48 = lean_uint32_dec_eq(x_45, x_47);
x_49 = l_instDecidableNot___redArg(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_18, 0, x_51);
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
lean_free_object(x_18);
x_52 = lean_mk_string_unchecked("external command '", 18, 18);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_dec(x_1);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = lean_mk_string_unchecked("' exited with code ", 19, 19);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = lean_uint32_to_nat(x_45);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_57);
x_59 = lean_string_append(x_56, x_58);
lean_dec(x_58);
x_60 = lean_box(3);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_62);
x_63 = lean_array_push(x_44, x_61);
x_6 = x_63;
x_7 = x_21;
goto block_10;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint32_t x_67; lean_object* x_68; uint32_t x_69; uint8_t x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_18, 1);
lean_inc(x_64);
lean_dec(x_18);
x_65 = lean_ctor_get(x_19, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_66 = x_19;
} else {
 lean_dec_ref(x_19);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get_uint32(x_16, sizeof(void*)*2);
lean_dec(x_16);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_uint32_of_nat(x_68);
x_70 = lean_uint32_dec_eq(x_67, x_69);
x_71 = l_instDecidableNot___redArg(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
lean_dec(x_1);
x_72 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
lean_dec(x_66);
x_75 = lean_mk_string_unchecked("external command '", 18, 18);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = lean_mk_string_unchecked("' exited with code ", 19, 19);
x_79 = lean_string_append(x_77, x_78);
lean_dec(x_78);
x_80 = lean_uint32_to_nat(x_67);
x_81 = l___private_Init_Data_Repr_0__Nat_reprFast(x_80);
x_82 = lean_string_append(x_79, x_81);
lean_dec(x_81);
x_83 = lean_box(3);
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_85);
x_86 = lean_array_push(x_65, x_84);
x_6 = x_86;
x_7 = x_64;
goto block_10;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_16);
lean_dec(x_1);
x_87 = lean_ctor_get(x_18, 1);
lean_inc(x_87);
lean_dec(x_18);
x_88 = lean_ctor_get(x_19, 1);
lean_inc(x_88);
lean_dec(x_19);
x_6 = x_88;
x_7 = x_87;
goto block_10;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_111 = lean_ctor_get(x_15, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_15, 1);
lean_inc(x_112);
lean_dec(x_15);
x_113 = lean_array_push(x_3, x_13);
x_114 = lean_mk_string_unchecked("failed to execute '", 19, 19);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_dec(x_1);
x_116 = lean_string_append(x_114, x_115);
lean_dec(x_115);
x_117 = lean_mk_string_unchecked("': ", 3, 3);
x_118 = lean_string_append(x_116, x_117);
lean_dec(x_117);
x_119 = lean_io_error_to_string(x_111);
x_120 = lean_string_append(x_118, x_119);
lean_dec(x_119);
x_121 = lean_box(3);
x_122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_unbox(x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_123);
x_124 = lean_array_push(x_113, x_122);
x_6 = x_124;
x_7 = x_112;
goto block_10;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lake_proc___lam__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_proc___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_proc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_proc(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_instDecidableEqPos(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_mk_string_unchecked("stderr:\n", 8, 8);
x_10 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_5, x_6, x_7);
x_11 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_5, x_10, x_6);
x_12 = lean_string_utf8_extract(x_5, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_box(0);
x_18 = lean_array_push(x_3, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Process_output(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
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
x_8 = lean_ctor_get_uint32(x_5, sizeof(void*)*2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_uint32_of_nat(x_9);
x_11 = lean_uint32_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_inc(x_1);
x_12 = l_Lake_mkCmdLog(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
x_16 = lean_array_get_size(x_2);
x_39 = lean_ctor_get(x_5, 0);
lean_inc(x_39);
x_40 = lean_string_utf8_byte_size(x_39);
x_41 = l_instDecidableEqPos(x_40, x_9);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_array_push(x_2, x_14);
x_43 = lean_mk_string_unchecked("stdout:\n", 8, 8);
x_44 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_39, x_40, x_9);
x_45 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_39, x_44, x_40);
x_46 = lean_string_utf8_extract(x_39, x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_39);
x_47 = lean_string_append(x_43, x_46);
lean_dec(x_46);
x_48 = lean_box(1);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_unbox(x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_50);
x_51 = lean_box(0);
x_52 = lean_array_push(x_42, x_49);
x_53 = l_Lake_captureProc___lam__0(x_5, x_51, x_52, x_6);
lean_dec(x_5);
x_22 = x_53;
goto block_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
lean_dec(x_39);
x_54 = lean_array_push(x_2, x_14);
x_55 = lean_box(0);
x_56 = l_Lake_captureProc___lam__0(x_5, x_55, x_54, x_6);
lean_dec(x_5);
x_22 = x_56;
goto block_38;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
if (lean_is_scalar(x_7)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_7;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
block_38:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_mk_string_unchecked("external command '", 18, 18);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_string_append(x_26, x_27);
lean_dec(x_27);
x_29 = lean_mk_string_unchecked("' exited with code ", 19, 19);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = lean_uint32_to_nat(x_8);
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_33 = lean_string_append(x_30, x_32);
lean_dec(x_32);
x_34 = lean_box(3);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_push(x_25, x_35);
x_17 = x_37;
x_18 = x_24;
goto block_21;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
lean_dec(x_5);
x_58 = lean_string_utf8_byte_size(x_57);
x_59 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_57, x_58, x_9);
x_60 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_57, x_59, x_58);
x_61 = lean_string_utf8_extract(x_57, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_2);
if (lean_is_scalar(x_7)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_7;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_6);
return x_63;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = lean_array_get_size(x_2);
x_67 = lean_mk_string_unchecked("failed to execute '", 19, 19);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_string_append(x_67, x_68);
lean_dec(x_68);
x_70 = lean_mk_string_unchecked("': ", 3, 3);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
x_72 = lean_io_error_to_string(x_65);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = lean_box(3);
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_unbox(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_76);
x_77 = lean_array_push(x_2, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_78);
return x_4;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_79 = lean_ctor_get(x_4, 0);
x_80 = lean_ctor_get(x_4, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_4);
x_81 = lean_array_get_size(x_2);
x_82 = lean_mk_string_unchecked("failed to execute '", 19, 19);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = lean_mk_string_unchecked("': ", 3, 3);
x_86 = lean_string_append(x_84, x_85);
lean_dec(x_85);
x_87 = lean_io_error_to_string(x_79);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = lean_box(3);
x_90 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_90, 0, x_88);
x_91 = lean_unbox(x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*1, x_91);
x_92 = lean_array_push(x_2, x_90);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_80);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_captureProc___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Process_output(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint32(x_5, sizeof(void*)*2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_uint32_of_nat(x_7);
x_9 = lean_uint32_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_box(0);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_string_utf8_byte_size(x_11);
x_13 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_11, x_12, x_7);
x_14 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_11, x_13, x_12);
x_15 = lean_string_utf8_extract(x_11, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_ctor_get_uint32(x_17, sizeof(void*)*2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_uint32_of_nat(x_20);
x_22 = lean_uint32_dec_eq(x_19, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_string_utf8_byte_size(x_25);
x_27 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_25, x_26, x_20);
x_28 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_25, x_27, x_26);
x_29 = lean_string_utf8_extract(x_25, x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_3, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_34);
return x_3;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_captureProc_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_captureProc_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_testProc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(0, 0, 3);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 0, x_9);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 2, x_11);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_8);
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_17);
x_19 = lean_io_process_spawn(x_18, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_io_process_child_wait(x_8, x_20, x_21);
lean_dec(x_20);
lean_dec(x_8);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint32_t x_26; uint32_t x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_uint32_of_nat(x_25);
x_27 = lean_unbox_uint32(x_24);
lean_dec(x_24);
x_28 = lean_uint32_dec_eq(x_27, x_26);
x_29 = lean_box(x_28);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; uint32_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_uint32_of_nat(x_32);
x_34 = lean_unbox_uint32(x_30);
lean_dec(x_30);
x_35 = lean_uint32_dec_eq(x_34, x_33);
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_3 = x_38;
goto block_6;
}
}
else
{
lean_object* x_39; 
lean_dec(x_8);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_3 = x_39;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_testProc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_testProc(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
