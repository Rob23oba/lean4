// Lean compiler output
// Module: Lean.Elab.Time
// Imports: Lean.Elab.Command
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
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0_spec__0(x_1, x_2, x_8, x_9, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Time_elabTimeCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Parser", 6, 6);
x_7 = lean_mk_string_unchecked("timeCmd", 7, 7);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5(lean_box(0), x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_io_mono_ms_now(x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Elab_Command_elabCommand(x_15, x_2, x_3, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_io_mono_ms_now(x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
x_26 = lean_mk_string_unchecked("time: ", 6, 6);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_nat_sub(x_22, x_12);
lean_dec(x_12);
lean_dec(x_22);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_31);
lean_ctor_set(x_20, 0, x_27);
x_32 = lean_mk_string_unchecked("ms", 2, 2);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_33);
lean_ctor_set(x_16, 0, x_20);
x_34 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_25, x_16, x_2, x_3, x_23);
lean_dec(x_3);
lean_dec(x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_1, x_37);
lean_dec(x_1);
x_39 = lean_mk_string_unchecked("time: ", 6, 6);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_nat_sub(x_35, x_12);
lean_dec(x_12);
lean_dec(x_35);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_41);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_MessageData_ofFormat(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("ms", 2, 2);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_47);
lean_ctor_set(x_16, 0, x_45);
x_48 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_38, x_16, x_2, x_3, x_36);
lean_dec(x_3);
lean_dec(x_38);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_io_mono_ms_now(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Syntax_getArg(x_1, x_54);
lean_dec(x_1);
x_56 = lean_mk_string_unchecked("time: ", 6, 6);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = lean_nat_sub(x_51, x_12);
lean_dec(x_12);
lean_dec(x_51);
x_59 = l___private_Init_Data_Repr_0__Nat_reprFast(x_58);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_MessageData_ofFormat(x_60);
if (lean_is_scalar(x_53)) {
 x_62 = lean_alloc_ctor(7, 2, 0);
} else {
 x_62 = x_53;
 lean_ctor_set_tag(x_62, 7);
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_mk_string_unchecked("ms", 2, 2);
x_64 = l_Lean_stringToMessageData(x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_55, x_65, x_2, x_3, x_52);
lean_dec(x_3);
lean_dec(x_55);
return x_66;
}
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logInfoAt___at___Lean_Elab_Time_elabTimeCmd_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("timeCmd", 7, 7);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_mk_string_unchecked("Elab", 4, 4);
x_8 = lean_mk_string_unchecked("Time", 4, 4);
x_9 = lean_mk_string_unchecked("elabTimeCmd", 11, 11);
x_10 = l_Lean_Name_mkStr4(x_3, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Time_elabTimeCmd), 4, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_6, x_10, x_11, x_1);
return x_12;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Time(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Time_elabTimeCmd__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
