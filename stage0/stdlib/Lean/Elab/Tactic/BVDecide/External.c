// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.External
// Imports: Std.Tactic.BVDecide.LRAT.Parser Lean.CoreM Std.Internal.Parsec
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
lean_object* lean_io_process_child_try_wait(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_satQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofUInt8(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parse(lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_CancelToken_isSet(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Internal_Parsec_manyCore___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_killAndWait(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_killAndWait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseHeader(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_satQuery(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___lam__0(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* lean_uint8_to_nat(uint8_t);
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_byte_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(uint8_t, size_t, size_t, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_io_process_child_kill(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_wsLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(32u);
x_9 = l_Char_ofNat(x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_uint8_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("expected: '", 11, 11);
x_14 = lean_uint8_to_nat(x_10);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
lean_inc(x_24);
lean_inc(x_2);
lean_ctor_set(x_1, 1, x_24);
x_28 = lean_nat_dec_lt(x_24, x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; uint32_t x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_byte_array_fget(x_2, x_24);
x_32 = lean_unsigned_to_nat(45u);
x_33 = l_Char_ofNat(x_32);
x_34 = lean_uint32_to_uint8(x_33);
x_35 = lean_uint8_dec_eq(x_31, x_34);
if (x_35 == 0)
{
lean_dec(x_4);
if (x_28 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
lean_dec(x_2);
x_36 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; uint32_t x_39; uint8_t x_40; uint8_t x_41; 
x_38 = lean_unsigned_to_nat(48u);
x_39 = l_Char_ofNat(x_38);
x_40 = lean_uint32_to_uint8(x_39);
x_41 = lean_uint8_dec_le(x_40, x_31);
if (x_41 == 0)
{
lean_dec(x_24);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_42; uint32_t x_43; uint8_t x_44; uint8_t x_45; 
x_42 = lean_unsigned_to_nat(57u);
x_43 = l_Char_ofNat(x_42);
x_44 = lean_uint32_to_uint8(x_43);
x_45 = lean_uint8_dec_le(x_31, x_44);
if (x_45 == 0)
{
lean_dec(x_24);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_46; lean_object* x_47; uint32_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_1);
x_46 = lean_nat_add(x_24, x_23);
lean_dec(x_24);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Char_ofUInt8(x_31);
x_49 = lean_uint32_to_uint8(x_48);
x_50 = lean_uint8_sub(x_49, x_40);
x_51 = lean_uint8_to_nat(x_50);
x_52 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_47, x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_54, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_nat_to_int(x_54);
lean_ctor_set(x_52, 1, x_58);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_59; 
lean_dec(x_54);
x_59 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 1, x_59);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_60, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_nat_to_int(x_60);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
x_66 = lean_mk_string_unchecked("id was 0", 8, 8);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
else
{
if (x_28 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_2);
x_68 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
if (x_35 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_2);
x_70 = lean_mk_string_unchecked("expected: '", 11, 11);
x_71 = lean_uint8_to_nat(x_34);
x_72 = l___private_Init_Data_Repr_0__Nat_reprFast(x_71);
x_73 = lean_string_append(x_70, x_72);
lean_dec(x_72);
x_74 = lean_mk_string_unchecked("'", 1, 1);
x_75 = lean_string_append(x_73, x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_82; 
lean_dec(x_1);
x_77 = lean_nat_add(x_24, x_23);
lean_dec(x_24);
lean_inc(x_77);
lean_inc(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_77);
x_82 = lean_nat_dec_lt(x_77, x_4);
lean_dec(x_4);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
lean_dec(x_2);
x_83 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
else
{
uint8_t x_85; lean_object* x_86; uint32_t x_87; uint8_t x_88; uint8_t x_89; 
x_85 = lean_byte_array_fget(x_2, x_77);
x_86 = lean_unsigned_to_nat(48u);
x_87 = l_Char_ofNat(x_86);
x_88 = lean_uint32_to_uint8(x_87);
x_89 = lean_uint8_dec_le(x_88, x_85);
if (x_89 == 0)
{
lean_dec(x_77);
lean_dec(x_2);
goto block_81;
}
else
{
lean_object* x_90; uint32_t x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_unsigned_to_nat(57u);
x_91 = l_Char_ofNat(x_90);
x_92 = lean_uint32_to_uint8(x_91);
x_93 = lean_uint8_dec_le(x_85, x_92);
if (x_93 == 0)
{
lean_dec(x_77);
lean_dec(x_2);
goto block_81;
}
else
{
lean_object* x_94; lean_object* x_95; uint32_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_78);
x_94 = lean_nat_add(x_77, x_23);
lean_dec(x_77);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Char_ofUInt8(x_85);
x_97 = lean_uint32_to_uint8(x_96);
x_98 = lean_uint8_sub(x_97, x_88);
x_99 = lean_uint8_to_nat(x_98);
x_100 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_95, x_99);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_nat_dec_eq(x_102, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_nat_to_int(x_102);
x_107 = lean_int_neg(x_106);
lean_dec(x_106);
lean_ctor_set(x_100, 1, x_107);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
else
{
lean_object* x_108; 
lean_dec(x_102);
x_108 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 1, x_108);
lean_ctor_set(x_100, 0, x_103);
return x_100;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_100, 0);
x_110 = lean_ctor_get(x_100, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_100);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_nat_dec_eq(x_109, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_nat_to_int(x_109);
x_114 = lean_int_neg(x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_109);
x_116 = lean_mk_string_unchecked("id was 0", 8, 8);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_110);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_mk_string_unchecked("digit expected", 14, 14);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_mk_string_unchecked("digit expected", 14, 14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_124; 
lean_dec(x_1);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_3, x_118);
lean_dec(x_3);
lean_inc(x_119);
lean_inc(x_2);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_2);
lean_ctor_set(x_120, 1, x_119);
x_124 = lean_nat_dec_lt(x_119, x_4);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_119);
lean_dec(x_4);
lean_dec(x_2);
x_125 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
else
{
uint8_t x_127; lean_object* x_128; uint32_t x_129; uint8_t x_130; uint8_t x_131; 
x_127 = lean_byte_array_fget(x_2, x_119);
x_128 = lean_unsigned_to_nat(45u);
x_129 = l_Char_ofNat(x_128);
x_130 = lean_uint32_to_uint8(x_129);
x_131 = lean_uint8_dec_eq(x_127, x_130);
if (x_131 == 0)
{
lean_dec(x_4);
if (x_124 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_119);
lean_dec(x_2);
x_132 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_120);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
else
{
lean_object* x_134; uint32_t x_135; uint8_t x_136; uint8_t x_137; 
x_134 = lean_unsigned_to_nat(48u);
x_135 = l_Char_ofNat(x_134);
x_136 = lean_uint32_to_uint8(x_135);
x_137 = lean_uint8_dec_le(x_136, x_127);
if (x_137 == 0)
{
lean_dec(x_119);
lean_dec(x_2);
goto block_123;
}
else
{
lean_object* x_138; uint32_t x_139; uint8_t x_140; uint8_t x_141; 
x_138 = lean_unsigned_to_nat(57u);
x_139 = l_Char_ofNat(x_138);
x_140 = lean_uint32_to_uint8(x_139);
x_141 = lean_uint8_dec_le(x_127, x_140);
if (x_141 == 0)
{
lean_dec(x_119);
lean_dec(x_2);
goto block_123;
}
else
{
lean_object* x_142; lean_object* x_143; uint32_t x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_120);
x_142 = lean_nat_add(x_119, x_118);
lean_dec(x_119);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_2);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Char_ofUInt8(x_127);
x_145 = lean_uint32_to_uint8(x_144);
x_146 = lean_uint8_sub(x_145, x_136);
x_147 = lean_uint8_to_nat(x_146);
x_148 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_143, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_unsigned_to_nat(0u);
x_153 = lean_nat_dec_eq(x_149, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_nat_to_int(x_149);
if (lean_is_scalar(x_151)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_151;
}
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_149);
x_156 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_151)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_151;
 lean_ctor_set_tag(x_157, 1);
}
lean_ctor_set(x_157, 0, x_150);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
}
else
{
if (x_124 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_119);
lean_dec(x_4);
lean_dec(x_2);
x_158 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_120);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
else
{
if (x_131 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_119);
lean_dec(x_4);
lean_dec(x_2);
x_160 = lean_mk_string_unchecked("expected: '", 11, 11);
x_161 = lean_uint8_to_nat(x_130);
x_162 = l___private_Init_Data_Repr_0__Nat_reprFast(x_161);
x_163 = lean_string_append(x_160, x_162);
lean_dec(x_162);
x_164 = lean_mk_string_unchecked("'", 1, 1);
x_165 = lean_string_append(x_163, x_164);
lean_dec(x_164);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_120);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_172; 
lean_dec(x_120);
x_167 = lean_nat_add(x_119, x_118);
lean_dec(x_119);
lean_inc(x_167);
lean_inc(x_2);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_2);
lean_ctor_set(x_168, 1, x_167);
x_172 = lean_nat_dec_lt(x_167, x_4);
lean_dec(x_4);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_2);
x_173 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_168);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
else
{
uint8_t x_175; lean_object* x_176; uint32_t x_177; uint8_t x_178; uint8_t x_179; 
x_175 = lean_byte_array_fget(x_2, x_167);
x_176 = lean_unsigned_to_nat(48u);
x_177 = l_Char_ofNat(x_176);
x_178 = lean_uint32_to_uint8(x_177);
x_179 = lean_uint8_dec_le(x_178, x_175);
if (x_179 == 0)
{
lean_dec(x_167);
lean_dec(x_2);
goto block_171;
}
else
{
lean_object* x_180; uint32_t x_181; uint8_t x_182; uint8_t x_183; 
x_180 = lean_unsigned_to_nat(57u);
x_181 = l_Char_ofNat(x_180);
x_182 = lean_uint32_to_uint8(x_181);
x_183 = lean_uint8_dec_le(x_175, x_182);
if (x_183 == 0)
{
lean_dec(x_167);
lean_dec(x_2);
goto block_171;
}
else
{
lean_object* x_184; lean_object* x_185; uint32_t x_186; uint8_t x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_dec(x_168);
x_184 = lean_nat_add(x_167, x_118);
lean_dec(x_167);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_2);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Char_ofUInt8(x_175);
x_187 = lean_uint32_to_uint8(x_186);
x_188 = lean_uint8_sub(x_187, x_178);
x_189 = lean_uint8_to_nat(x_188);
x_190 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_185, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_194 = lean_unsigned_to_nat(0u);
x_195 = lean_nat_dec_eq(x_191, x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_nat_to_int(x_191);
x_197 = lean_int_neg(x_196);
lean_dec(x_196);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_193;
}
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_191);
x_199 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_193)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_193;
 lean_ctor_set_tag(x_200, 1);
}
lean_ctor_set(x_200, 0, x_192);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
block_171:
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_mk_string_unchecked("digit expected", 14, 14);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
}
block_123:
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_mk_string_unchecked("digit expected", 14, 14);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Internal_Parsec_manyCore___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_21 = lean_byte_array_size(x_8);
x_22 = lean_nat_dec_lt(x_9, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_8);
x_23 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_23;
goto block_16;
}
else
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_unsigned_to_nat(32u);
x_25 = l_Char_ofNat(x_24);
x_26 = lean_uint32_to_uint8(x_25);
x_27 = lean_byte_array_fget(x_8, x_9);
x_28 = lean_uint8_dec_eq(x_27, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
lean_dec(x_8);
x_29 = lean_mk_string_unchecked("expected: '", 11, 11);
x_30 = lean_uint8_to_nat(x_26);
x_31 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_32 = lean_string_append(x_29, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("'", 1, 1);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_10 = x_2;
x_11 = x_34;
goto block_16;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_9, x_35);
x_37 = lean_nat_dec_lt(x_36, x_21);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
x_38 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_38;
goto block_16;
}
else
{
uint8_t x_39; lean_object* x_40; uint32_t x_41; uint8_t x_42; uint8_t x_43; 
x_39 = lean_byte_array_fget(x_8, x_36);
x_40 = lean_unsigned_to_nat(45u);
x_41 = l_Char_ofNat(x_40);
x_42 = lean_uint32_to_uint8(x_41);
x_43 = lean_uint8_dec_eq(x_39, x_42);
if (x_43 == 0)
{
lean_dec(x_21);
if (x_37 == 0)
{
lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_8);
x_44 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_44;
goto block_16;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_unsigned_to_nat(48u);
x_46 = l_Char_ofNat(x_45);
x_47 = lean_uint32_to_uint8(x_46);
x_48 = lean_uint8_dec_le(x_47, x_39);
if (x_48 == 0)
{
lean_dec(x_36);
lean_dec(x_8);
goto block_18;
}
else
{
lean_object* x_49; uint32_t x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_unsigned_to_nat(57u);
x_50 = l_Char_ofNat(x_49);
x_51 = lean_uint32_to_uint8(x_50);
x_52 = lean_uint8_dec_le(x_39, x_51);
if (x_52 == 0)
{
lean_dec(x_36);
lean_dec(x_8);
goto block_18;
}
else
{
lean_object* x_53; lean_object* x_54; uint32_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_53 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Char_ofUInt8(x_39);
x_56 = lean_uint32_to_uint8(x_55);
x_57 = lean_uint8_sub(x_56, x_47);
x_58 = lean_uint8_to_nat(x_57);
x_59 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_54, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_60, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_9);
lean_dec(x_2);
x_64 = lean_nat_to_int(x_60);
x_3 = x_61;
x_4 = x_64;
goto block_7;
}
else
{
lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
x_65 = lean_mk_string_unchecked("id was 0", 8, 8);
x_10 = x_2;
x_11 = x_65;
goto block_16;
}
}
}
}
}
else
{
if (x_37 == 0)
{
lean_object* x_66; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
x_66 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_66;
goto block_16;
}
else
{
if (x_43 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
x_67 = lean_mk_string_unchecked("expected: '", 11, 11);
x_68 = lean_uint8_to_nat(x_42);
x_69 = l___private_Init_Data_Repr_0__Nat_reprFast(x_68);
x_70 = lean_string_append(x_67, x_69);
lean_dec(x_69);
x_71 = lean_mk_string_unchecked("'", 1, 1);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_10 = x_2;
x_11 = x_72;
goto block_16;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_74 = lean_nat_dec_lt(x_73, x_21);
lean_dec(x_21);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_73);
lean_dec(x_8);
x_75 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_75;
goto block_16;
}
else
{
uint8_t x_76; lean_object* x_77; uint32_t x_78; uint8_t x_79; uint8_t x_80; 
x_76 = lean_byte_array_fget(x_8, x_73);
x_77 = lean_unsigned_to_nat(48u);
x_78 = l_Char_ofNat(x_77);
x_79 = lean_uint32_to_uint8(x_78);
x_80 = lean_uint8_dec_le(x_79, x_76);
if (x_80 == 0)
{
lean_dec(x_73);
lean_dec(x_8);
goto block_20;
}
else
{
lean_object* x_81; uint32_t x_82; uint8_t x_83; uint8_t x_84; 
x_81 = lean_unsigned_to_nat(57u);
x_82 = l_Char_ofNat(x_81);
x_83 = lean_uint32_to_uint8(x_82);
x_84 = lean_uint8_dec_le(x_76, x_83);
if (x_84 == 0)
{
lean_dec(x_73);
lean_dec(x_8);
goto block_20;
}
else
{
lean_object* x_85; lean_object* x_86; uint32_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_85 = lean_nat_add(x_73, x_35);
lean_dec(x_73);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_8);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Char_ofUInt8(x_76);
x_88 = lean_uint32_to_uint8(x_87);
x_89 = lean_uint8_sub(x_88, x_79);
x_90 = lean_uint8_to_nat(x_89);
x_91 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_86, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_92, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_9);
lean_dec(x_2);
x_96 = lean_nat_to_int(x_92);
x_97 = lean_int_neg(x_96);
lean_dec(x_96);
x_3 = x_93;
x_4 = x_97;
goto block_7;
}
else
{
lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_92);
x_98 = lean_mk_string_unchecked("id was 0", 8, 8);
x_10 = x_2;
x_11 = x_98;
goto block_16;
}
}
}
}
}
}
}
}
}
}
block_7:
{
lean_object* x_5; 
x_5 = lean_array_push(x_1, x_4);
x_1 = x_5;
x_2 = x_3;
goto _start;
}
block_16:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_1);
return x_15;
}
}
block_18:
{
lean_object* x_17; 
x_17 = lean_mk_string_unchecked("digit expected", 14, 14);
x_10 = x_2;
x_11 = x_17;
goto block_16;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_mk_string_unchecked("digit expected", 14, 14);
x_10 = x_2;
x_11 = x_19;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_21; uint8_t x_22; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_21 = lean_byte_array_size(x_8);
x_22 = lean_nat_dec_lt(x_9, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_8);
x_23 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_23;
goto block_16;
}
else
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_unsigned_to_nat(32u);
x_25 = l_Char_ofNat(x_24);
x_26 = lean_uint32_to_uint8(x_25);
x_27 = lean_byte_array_fget(x_8, x_9);
x_28 = lean_uint8_dec_eq(x_27, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
lean_dec(x_8);
x_29 = lean_mk_string_unchecked("expected: '", 11, 11);
x_30 = lean_uint8_to_nat(x_26);
x_31 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_32 = lean_string_append(x_29, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("'", 1, 1);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_10 = x_2;
x_11 = x_34;
goto block_16;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_9, x_35);
x_37 = lean_nat_dec_lt(x_36, x_21);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
x_38 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_38;
goto block_16;
}
else
{
uint8_t x_39; lean_object* x_40; uint32_t x_41; uint8_t x_42; uint8_t x_43; 
x_39 = lean_byte_array_fget(x_8, x_36);
x_40 = lean_unsigned_to_nat(45u);
x_41 = l_Char_ofNat(x_40);
x_42 = lean_uint32_to_uint8(x_41);
x_43 = lean_uint8_dec_eq(x_39, x_42);
if (x_43 == 0)
{
lean_dec(x_21);
if (x_37 == 0)
{
lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_8);
x_44 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_44;
goto block_16;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_unsigned_to_nat(48u);
x_46 = l_Char_ofNat(x_45);
x_47 = lean_uint32_to_uint8(x_46);
x_48 = lean_uint8_dec_le(x_47, x_39);
if (x_48 == 0)
{
lean_dec(x_36);
lean_dec(x_8);
goto block_18;
}
else
{
lean_object* x_49; uint32_t x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_unsigned_to_nat(57u);
x_50 = l_Char_ofNat(x_49);
x_51 = lean_uint32_to_uint8(x_50);
x_52 = lean_uint8_dec_le(x_39, x_51);
if (x_52 == 0)
{
lean_dec(x_36);
lean_dec(x_8);
goto block_18;
}
else
{
lean_object* x_53; lean_object* x_54; uint32_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_53 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Char_ofUInt8(x_39);
x_56 = lean_uint32_to_uint8(x_55);
x_57 = lean_uint8_sub(x_56, x_47);
x_58 = lean_uint8_to_nat(x_57);
x_59 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_54, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_60, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_9);
lean_dec(x_2);
x_64 = lean_nat_to_int(x_60);
x_3 = x_61;
x_4 = x_64;
goto block_7;
}
else
{
lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
x_65 = lean_mk_string_unchecked("id was 0", 8, 8);
x_10 = x_2;
x_11 = x_65;
goto block_16;
}
}
}
}
}
else
{
if (x_37 == 0)
{
lean_object* x_66; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
x_66 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_66;
goto block_16;
}
else
{
if (x_43 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
x_67 = lean_mk_string_unchecked("expected: '", 11, 11);
x_68 = lean_uint8_to_nat(x_42);
x_69 = l___private_Init_Data_Repr_0__Nat_reprFast(x_68);
x_70 = lean_string_append(x_67, x_69);
lean_dec(x_69);
x_71 = lean_mk_string_unchecked("'", 1, 1);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_10 = x_2;
x_11 = x_72;
goto block_16;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_74 = lean_nat_dec_lt(x_73, x_21);
lean_dec(x_21);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_73);
lean_dec(x_8);
x_75 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = x_2;
x_11 = x_75;
goto block_16;
}
else
{
uint8_t x_76; lean_object* x_77; uint32_t x_78; uint8_t x_79; uint8_t x_80; 
x_76 = lean_byte_array_fget(x_8, x_73);
x_77 = lean_unsigned_to_nat(48u);
x_78 = l_Char_ofNat(x_77);
x_79 = lean_uint32_to_uint8(x_78);
x_80 = lean_uint8_dec_le(x_79, x_76);
if (x_80 == 0)
{
lean_dec(x_73);
lean_dec(x_8);
goto block_20;
}
else
{
lean_object* x_81; uint32_t x_82; uint8_t x_83; uint8_t x_84; 
x_81 = lean_unsigned_to_nat(57u);
x_82 = l_Char_ofNat(x_81);
x_83 = lean_uint32_to_uint8(x_82);
x_84 = lean_uint8_dec_le(x_76, x_83);
if (x_84 == 0)
{
lean_dec(x_73);
lean_dec(x_8);
goto block_20;
}
else
{
lean_object* x_85; lean_object* x_86; uint32_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_85 = lean_nat_add(x_73, x_35);
lean_dec(x_73);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_8);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Char_ofUInt8(x_76);
x_88 = lean_uint32_to_uint8(x_87);
x_89 = lean_uint8_sub(x_88, x_79);
x_90 = lean_uint8_to_nat(x_89);
x_91 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_86, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_92, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_9);
lean_dec(x_2);
x_96 = lean_nat_to_int(x_92);
x_97 = lean_int_neg(x_96);
lean_dec(x_96);
x_3 = x_93;
x_4 = x_97;
goto block_7;
}
else
{
lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_92);
x_98 = lean_mk_string_unchecked("id was 0", 8, 8);
x_10 = x_2;
x_11 = x_98;
goto block_16;
}
}
}
}
}
}
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_push(x_1, x_4);
x_6 = l_Std_Internal_Parsec_manyCore___at___Std_Internal_Parsec_manyCore___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0_spec__0(x_5, x_3);
return x_6;
}
block_16:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_1);
return x_15;
}
}
block_18:
{
lean_object* x_17; 
x_17 = lean_mk_string_unchecked("digit expected", 14, 14);
x_10 = x_2;
x_11 = x_17;
goto block_16;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_mk_string_unchecked("digit expected", 14, 14);
x_10 = x_2;
x_11 = x_19;
goto block_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_dec_lt(x_17, x_6);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_nat_abs(x_6);
lean_dec(x_6);
x_20 = lean_box(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_9 = x_21;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_nat_abs(x_6);
lean_dec(x_6);
x_23 = lean_box(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_9 = x_24;
goto block_15;
}
block_15:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(118u);
x_9 = l_Char_ofNat(x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_uint8_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("expected: '", 11, 11);
x_14 = lean_uint8_to_nat(x_10);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = l_Std_Internal_Parsec_manyCore___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(x_26, x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_array_size(x_29);
x_32 = lean_usize_of_nat(x_25);
x_33 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(x_5, x_31, x_32, x_29);
x_39 = lean_mk_string_unchecked(" 0", 2, 2);
x_40 = lean_string_to_utf8(x_39);
lean_dec(x_39);
lean_inc(x_28);
x_41 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_40, x_28);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_30);
lean_dec(x_28);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 1);
lean_dec(x_43);
x_44 = lean_box(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_41, 1, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(x_5);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_33);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_dec(x_28);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
x_55 = lean_nat_dec_eq(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_33);
lean_dec(x_30);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_74; uint8_t x_75; 
lean_dec(x_51);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
x_74 = lean_byte_array_size(x_57);
x_75 = lean_nat_dec_lt(x_58, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_57);
x_76 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_59 = x_50;
x_60 = x_76;
goto block_73;
}
else
{
lean_object* x_77; uint32_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; 
x_77 = lean_unsigned_to_nat(10u);
x_78 = l_Char_ofNat(x_77);
x_79 = lean_uint32_to_uint8(x_78);
x_80 = lean_byte_array_fget(x_57, x_58);
x_81 = lean_uint8_dec_eq(x_80, x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_57);
x_82 = lean_mk_string_unchecked("expected: '", 11, 11);
x_83 = lean_uint8_to_nat(x_79);
x_84 = l___private_Init_Data_Repr_0__Nat_reprFast(x_83);
x_85 = lean_string_append(x_82, x_84);
lean_dec(x_84);
x_86 = lean_mk_string_unchecked("'", 1, 1);
x_87 = lean_string_append(x_85, x_86);
lean_dec(x_86);
x_59 = x_50;
x_60 = x_87;
goto block_73;
}
else
{
uint8_t x_88; 
lean_dec(x_52);
x_88 = !lean_is_exclusive(x_50);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_50, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_50, 0);
lean_dec(x_90);
x_91 = lean_nat_add(x_58, x_23);
lean_dec(x_58);
lean_ctor_set(x_50, 1, x_91);
x_34 = x_50;
goto block_38;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_50);
x_92 = lean_nat_add(x_58, x_23);
lean_dec(x_58);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_57);
lean_ctor_set(x_93, 1, x_92);
x_34 = x_93;
goto block_38;
}
}
}
block_73:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_nat_dec_eq(x_58, x_61);
lean_dec(x_61);
lean_dec(x_58);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_33);
lean_dec(x_30);
if (lean_is_scalar(x_52)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_52;
}
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_60);
lean_dec(x_52);
x_64 = lean_mk_string_unchecked("\r\n", 2, 2);
x_65 = lean_string_to_utf8(x_64);
lean_dec(x_64);
x_66 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_65, x_59);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_34 = x_67;
goto block_38;
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_34 = x_68;
goto block_38;
}
else
{
uint8_t x_69; 
lean_dec(x_33);
lean_dec(x_30);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
}
}
block_38:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_27);
if (x_94 == 0)
{
return x_27;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_27, 0);
x_96 = lean_ctor_get(x_27, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_27);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_3, x_98);
lean_dec(x_3);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_mk_empty_array_with_capacity(x_101);
x_103 = l_Std_Internal_Parsec_manyCore___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__0(x_102, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_array_size(x_105);
x_108 = lean_usize_of_nat(x_101);
x_109 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(x_5, x_107, x_108, x_105);
x_115 = lean_mk_string_unchecked(" 0", 2, 2);
x_116 = lean_string_to_utf8(x_115);
lean_dec(x_115);
lean_inc(x_104);
x_117 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_116, x_104);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_106);
lean_dec(x_104);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(x_5);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_109);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_117, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_125 = x_117;
} else {
 lean_dec_ref(x_117);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_104, 1);
lean_inc(x_126);
lean_dec(x_104);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
x_128 = lean_nat_dec_eq(x_126, x_127);
lean_dec(x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_109);
lean_dec(x_106);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_124);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_147; uint8_t x_148; 
lean_dec(x_124);
x_130 = lean_ctor_get(x_123, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 1);
lean_inc(x_131);
x_147 = lean_byte_array_size(x_130);
x_148 = lean_nat_dec_lt(x_131, x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_130);
x_149 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_132 = x_123;
x_133 = x_149;
goto block_146;
}
else
{
lean_object* x_150; uint32_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; 
x_150 = lean_unsigned_to_nat(10u);
x_151 = l_Char_ofNat(x_150);
x_152 = lean_uint32_to_uint8(x_151);
x_153 = lean_byte_array_fget(x_130, x_131);
x_154 = lean_uint8_dec_eq(x_153, x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_130);
x_155 = lean_mk_string_unchecked("expected: '", 11, 11);
x_156 = lean_uint8_to_nat(x_152);
x_157 = l___private_Init_Data_Repr_0__Nat_reprFast(x_156);
x_158 = lean_string_append(x_155, x_157);
lean_dec(x_157);
x_159 = lean_mk_string_unchecked("'", 1, 1);
x_160 = lean_string_append(x_158, x_159);
lean_dec(x_159);
x_132 = x_123;
x_133 = x_160;
goto block_146;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_161 = x_123;
} else {
 lean_dec_ref(x_123);
 x_161 = lean_box(0);
}
x_162 = lean_nat_add(x_131, x_98);
lean_dec(x_131);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_130);
lean_ctor_set(x_163, 1, x_162);
x_110 = x_163;
goto block_114;
}
}
block_146:
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
x_135 = lean_nat_dec_eq(x_131, x_134);
lean_dec(x_134);
lean_dec(x_131);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_109);
lean_dec(x_106);
if (lean_is_scalar(x_125)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_125;
}
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_133);
lean_dec(x_125);
x_137 = lean_mk_string_unchecked("\r\n", 2, 2);
x_138 = lean_string_to_utf8(x_137);
lean_dec(x_137);
x_139 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_138, x_132);
lean_dec(x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_110 = x_140;
goto block_114;
}
else
{
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_110 = x_141;
goto block_114;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_109);
lean_dec(x_106);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
}
}
block_114:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
if (lean_is_scalar(x_106)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_106;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_103, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_103, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_166 = x_103;
} else {
 lean_dec_ref(x_103);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment_spec__2(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parsePartialAssignment(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Array_append(lean_box(0), x_1, x_8);
lean_dec(x_8);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_free_object(x_3);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_9);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Array_append(lean_box(0), x_1, x_15);
lean_dec(x_15);
x_17 = lean_unbox(x_14);
lean_dec(x_14);
if (x_17 == 0)
{
x_1 = x_16;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines_go(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseHeader(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("s SATISFIABLE", 13, 13);
x_3 = lean_string_to_utf8(x_2);
lean_dec(x_2);
x_4 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_3, x_1);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_24 = lean_byte_array_size(x_7);
x_25 = lean_nat_dec_lt(x_8, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_7);
x_26 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_9 = x_5;
x_10 = x_26;
goto block_23;
}
else
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(10u);
x_28 = l_Char_ofNat(x_27);
x_29 = lean_uint32_to_uint8(x_28);
x_30 = lean_byte_array_fget(x_7, x_8);
x_31 = lean_uint8_dec_eq(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
x_32 = lean_mk_string_unchecked("expected: '", 11, 11);
x_33 = lean_uint8_to_nat(x_29);
x_34 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked("'", 1, 1);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_9 = x_5;
x_10 = x_37;
goto block_23;
}
else
{
uint8_t x_38; 
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_5, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_5, 0);
lean_dec(x_40);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_8, x_41);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_42);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_8, x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_7);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
block_23:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
if (lean_is_scalar(x_6)) {
 x_13 = lean_alloc_ctor(1, 2, 0);
} else {
 x_13 = x_6;
 lean_ctor_set_tag(x_13, 1);
}
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_mk_string_unchecked("\r\n", 2, 2);
x_15 = lean_string_to_utf8(x_14);
lean_dec(x_14);
x_16 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_15, x_9);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 1, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
return x_16;
}
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_mk_string_unchecked("s SATISFIABLE", 13, 13);
x_11 = lean_string_to_utf8(x_10);
lean_dec(x_10);
x_12 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_28; uint8_t x_29; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_28 = lean_byte_array_size(x_15);
x_29 = lean_nat_dec_lt(x_16, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_15);
x_30 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_17 = x_13;
x_18 = x_30;
goto block_27;
}
else
{
lean_object* x_31; uint32_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(10u);
x_32 = l_Char_ofNat(x_31);
x_33 = lean_uint32_to_uint8(x_32);
x_34 = lean_byte_array_fget(x_15, x_16);
x_35 = lean_uint8_dec_eq(x_34, x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_15);
x_36 = lean_mk_string_unchecked("expected: '", 11, 11);
x_37 = lean_uint8_to_nat(x_33);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_37);
x_39 = lean_string_append(x_36, x_38);
lean_dec(x_38);
x_40 = lean_mk_string_unchecked("'", 1, 1);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_17 = x_13;
x_18 = x_41;
goto block_27;
}
else
{
uint8_t x_42; 
lean_dec(x_14);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_13, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_13, 0);
lean_dec(x_44);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_16, x_45);
lean_dec(x_16);
lean_ctor_set(x_13, 1, x_46);
x_47 = l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines(x_13);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_16, x_48);
lean_dec(x_16);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_15);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines(x_50);
return x_51;
}
}
}
block_27:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
if (lean_is_scalar(x_14)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_14;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_14);
x_22 = lean_mk_string_unchecked("\r\n", 2, 2);
x_23 = lean_string_to_utf8(x_22);
lean_dec(x_22);
x_24 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_23, x_17);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines(x_25);
return x_26;
}
else
{
x_2 = x_24;
goto block_9;
}
}
}
}
else
{
x_2 = x_12;
goto block_9;
}
block_9:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parseLines(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_interruptExceptionId;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 11);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_CancelToken_isSet(x_8, x_5);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_apply_3(x_2, x_3, x_4, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_apply_3(x_1, x_3, x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___redArg(x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwInterruptException___at___Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(1);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_killAndWait(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_kill(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_io_process_child_wait(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_killAndWait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_killAndWait(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_killAndWait(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_io_error_to_string(x_12);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_ctor_get(x_3, 5);
x_21 = lean_io_error_to_string(x_18);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
lean_inc(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = lean_io_process_child_try_wait(x_1, x_2, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(50u);
x_14 = lean_uint32_of_nat(x_13);
x_15 = l_IO_sleep(x_14, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_nat_sub(x_3, x_13);
x_18 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go(x_1, x_17, x_2, x_4, x_5, x_6, x_7, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_task_get_own(x_4);
x_23 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_22, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_task_get_own(x_5);
x_27 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_26, x_25);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint32_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_unbox_uint32(x_21);
lean_dec(x_21);
lean_ctor_set_uint32(x_30, sizeof(void*)*2, x_31);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_30);
lean_ctor_set(x_27, 0, x_11);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_unbox_uint32(x_21);
lean_dec(x_21);
lean_ctor_set_uint32(x_34, sizeof(void*)*2, x_35);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_24);
lean_dec(x_21);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_io_error_to_string(x_38);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_39);
x_40 = l_Lean_MessageData_ofFormat(x_11);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_27, 0, x_41);
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_io_error_to_string(x_42);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_44);
x_45 = l_Lean_MessageData_ofFormat(x_11);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_21);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_23, 0);
x_50 = lean_io_error_to_string(x_49);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_50);
x_51 = l_Lean_MessageData_ofFormat(x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_9);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_23, 0, x_52);
return x_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_23);
x_55 = lean_io_error_to_string(x_53);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_55);
x_56 = l_Lean_MessageData_ofFormat(x_11);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_9);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = lean_task_get_own(x_4);
x_61 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_60, x_19);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_task_get_own(x_5);
x_65 = l_IO_ofExcept___at___IO_Process_output_spec__0___redArg(x_64, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_9);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_66);
x_70 = lean_unbox_uint32(x_59);
lean_dec(x_59);
lean_ctor_set_uint32(x_69, sizeof(void*)*2, x_70);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_62);
lean_dec(x_59);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_io_error_to_string(x_73);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_MessageData_ofFormat(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_9);
lean_ctor_set(x_79, 1, x_78);
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_59);
lean_dec(x_5);
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_61, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_83 = x_61;
} else {
 lean_dec_ref(x_61);
 x_83 = lean_box(0);
}
x_84 = lean_io_error_to_string(x_81);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Lean_MessageData_ofFormat(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_9);
lean_ctor_set(x_87, 1, x_86);
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_10);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_10, 0);
x_91 = lean_io_error_to_string(x_90);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_MessageData_ofFormat(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_9);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_10, 0, x_94);
return x_10;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_10, 0);
x_96 = lean_ctor_get(x_10, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_10);
x_97 = lean_io_error_to_string(x_95);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lean_MessageData_ofFormat(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_9);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_3);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed), 5, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed), 8, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withInterruptCheck), 6, 3);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_withTimeoutCheck___redArg(x_2, x_9, x_11, x_6, x_7, x_8);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_readToEnd(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_box(2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 0, 3);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, 0, x_9);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, 2, x_11);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
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
x_19 = lean_io_process_spawn(x_18, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(9u);
x_25 = lean_io_as_task(x_23, x_24, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_20, 2);
lean_inc(x_28);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_io_as_task(x_29, x_24, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1000u);
x_34 = lean_nat_mul(x_1, x_33);
x_35 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible_go(x_8, x_34, x_20, x_26, x_31, x_3, x_4, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_3, 5);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_io_error_to_string(x_37);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_19, 0, x_42);
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_ctor_get(x_3, 5);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_io_error_to_string(x_43);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_runInterruptible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_satQuery(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_mk_string_unchecked("--lrat", 6, 6);
x_10 = lean_mk_string_unchecked("--binary=", 9, 9);
if (x_5 == 0)
{
lean_object* x_225; 
x_225 = lean_mk_string_unchecked("false", 5, 5);
x_11 = x_225;
goto block_224;
}
else
{
lean_object* x_226; 
x_226 = lean_mk_string_unchecked("true", 4, 4);
x_11 = x_226;
goto block_224;
}
block_224:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_mk_string_unchecked("--quiet", 7, 7);
x_14 = lean_mk_string_unchecked("--unsat", 7, 7);
x_15 = lean_mk_string_unchecked("--shrink=0", 10, 10);
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = lean_array_push(x_17, x_2);
x_19 = lean_array_push(x_18, x_3);
x_20 = lean_array_push(x_19, x_9);
x_21 = lean_array_push(x_20, x_12);
x_22 = lean_array_push(x_21, x_13);
x_23 = lean_array_push(x_22, x_14);
x_24 = lean_array_push(x_23, x_15);
x_25 = lean_box(0);
x_26 = lean_box(2);
x_27 = lean_alloc_ctor(0, 0, 3);
x_28 = lean_unbox(x_25);
lean_ctor_set_uint8(x_27, 0, x_28);
x_29 = lean_unbox(x_25);
lean_ctor_set_uint8(x_27, 1, x_29);
x_30 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, 2, x_30);
x_31 = lean_box(0);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_box(1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_1);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_33);
x_37 = lean_unbox(x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_37);
x_38 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*5 + 1, x_38);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_Elab_Tactic_BVDecide_External_runInterruptible(x_4, x_36, x_6, x_7, x_8);
lean_dec(x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_39, 0);
lean_dec(x_45);
x_46 = lean_ctor_get_uint32(x_43, sizeof(void*)*2);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_unsigned_to_nat(255u);
x_50 = lean_uint32_of_nat(x_49);
x_51 = lean_uint32_dec_eq(x_46, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = lean_mk_string_unchecked("s UNSATISFIABLE", 15, 15);
x_53 = lean_string_utf8_byte_size(x_47);
lean_inc(x_47);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_32);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_unsigned_to_nat(15u);
x_56 = l_Substring_nextn(x_54, x_55, x_32);
lean_inc(x_47);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_32);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_string_utf8_byte_size(x_52);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_32);
lean_ctor_set(x_59, 2, x_58);
x_60 = l_Substring_beq(x_57, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_61 = lean_mk_string_unchecked("s SATISFIABLE", 13, 13);
x_62 = lean_unsigned_to_nat(13u);
x_63 = l_Substring_nextn(x_54, x_62, x_32);
lean_dec(x_54);
lean_inc(x_47);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_32);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_string_utf8_byte_size(x_61);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_32);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_Substring_beq(x_64, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_39);
x_68 = lean_mk_string_unchecked("The external prover produced unexpected output, stdout:\n", 56, 56);
x_69 = lean_string_append(x_68, x_47);
lean_dec(x_47);
x_70 = lean_mk_string_unchecked("stderr:\n", 8, 8);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
x_72 = lean_string_append(x_71, x_48);
lean_dec(x_48);
lean_ctor_set_tag(x_40, 3);
lean_ctor_set(x_40, 0, x_72);
x_73 = l_Lean_MessageData_ofFormat(x_40);
x_74 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_73, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_48);
lean_free_object(x_40);
x_75 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parse), 1, 0);
x_76 = lean_string_to_utf8(x_47);
x_77 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_75, x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
lean_free_object(x_39);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_mk_string_unchecked("Error ", 6, 6);
x_81 = lean_string_append(x_80, x_79);
lean_dec(x_79);
x_82 = lean_mk_string_unchecked(" while parsing:\n", 16, 16);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_string_append(x_83, x_47);
lean_dec(x_47);
lean_ctor_set_tag(x_77, 3);
lean_ctor_set(x_77, 0, x_84);
x_85 = l_Lean_MessageData_ofFormat(x_77);
x_86 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_85, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_77, 0);
lean_inc(x_87);
lean_dec(x_77);
x_88 = lean_mk_string_unchecked("Error ", 6, 6);
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
x_90 = lean_mk_string_unchecked(" while parsing:\n", 16, 16);
x_91 = lean_string_append(x_89, x_90);
lean_dec(x_90);
x_92 = lean_string_append(x_91, x_47);
lean_dec(x_47);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_94, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_6);
x_96 = !lean_is_exclusive(x_77);
if (x_96 == 0)
{
lean_ctor_set_tag(x_77, 0);
lean_ctor_set(x_39, 0, x_77);
return x_39;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_77, 0);
lean_inc(x_97);
lean_dec(x_77);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_39, 0, x_98);
return x_39;
}
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_47);
lean_free_object(x_40);
lean_dec(x_7);
lean_dec(x_6);
x_99 = lean_box(1);
lean_ctor_set(x_39, 0, x_99);
return x_39;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_47);
lean_free_object(x_39);
x_100 = lean_mk_string_unchecked("Failed to execute external prover:\n", 35, 35);
x_101 = lean_string_append(x_100, x_48);
lean_dec(x_48);
lean_ctor_set_tag(x_40, 3);
lean_ctor_set(x_40, 0, x_101);
x_102 = l_Lean_MessageData_ofFormat(x_40);
x_103 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_102, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint32_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint32_t x_110; uint8_t x_111; 
x_104 = lean_ctor_get(x_40, 0);
x_105 = lean_ctor_get(x_39, 1);
lean_inc(x_105);
lean_dec(x_39);
x_106 = lean_ctor_get_uint32(x_104, sizeof(void*)*2);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_unsigned_to_nat(255u);
x_110 = lean_uint32_of_nat(x_109);
x_111 = lean_uint32_dec_eq(x_106, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_112 = lean_mk_string_unchecked("s UNSATISFIABLE", 15, 15);
x_113 = lean_string_utf8_byte_size(x_107);
lean_inc(x_107);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_32);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_unsigned_to_nat(15u);
x_116 = l_Substring_nextn(x_114, x_115, x_32);
lean_inc(x_107);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_32);
lean_ctor_set(x_117, 2, x_116);
x_118 = lean_string_utf8_byte_size(x_112);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_32);
lean_ctor_set(x_119, 2, x_118);
x_120 = l_Substring_beq(x_117, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_121 = lean_mk_string_unchecked("s SATISFIABLE", 13, 13);
x_122 = lean_unsigned_to_nat(13u);
x_123 = l_Substring_nextn(x_114, x_122, x_32);
lean_dec(x_114);
lean_inc(x_107);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_107);
lean_ctor_set(x_124, 1, x_32);
lean_ctor_set(x_124, 2, x_123);
x_125 = lean_string_utf8_byte_size(x_121);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_32);
lean_ctor_set(x_126, 2, x_125);
x_127 = l_Substring_beq(x_124, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_mk_string_unchecked("The external prover produced unexpected output, stdout:\n", 56, 56);
x_129 = lean_string_append(x_128, x_107);
lean_dec(x_107);
x_130 = lean_mk_string_unchecked("stderr:\n", 8, 8);
x_131 = lean_string_append(x_129, x_130);
lean_dec(x_130);
x_132 = lean_string_append(x_131, x_108);
lean_dec(x_108);
lean_ctor_set_tag(x_40, 3);
lean_ctor_set(x_40, 0, x_132);
x_133 = l_Lean_MessageData_ofFormat(x_40);
x_134 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_133, x_6, x_7, x_105);
lean_dec(x_7);
lean_dec(x_6);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_108);
lean_free_object(x_40);
x_135 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parse), 1, 0);
x_136 = lean_string_to_utf8(x_107);
x_137 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_135, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = lean_mk_string_unchecked("Error ", 6, 6);
x_141 = lean_string_append(x_140, x_138);
lean_dec(x_138);
x_142 = lean_mk_string_unchecked(" while parsing:\n", 16, 16);
x_143 = lean_string_append(x_141, x_142);
lean_dec(x_142);
x_144 = lean_string_append(x_143, x_107);
lean_dec(x_107);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(3, 1, 0);
} else {
 x_145 = x_139;
 lean_ctor_set_tag(x_145, 3);
}
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Lean_MessageData_ofFormat(x_145);
x_147 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_146, x_6, x_7, x_105);
lean_dec(x_7);
lean_dec(x_6);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
x_148 = lean_ctor_get(x_137, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_149 = x_137;
} else {
 lean_dec_ref(x_137);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 1, 0);
} else {
 x_150 = x_149;
 lean_ctor_set_tag(x_150, 0);
}
lean_ctor_set(x_150, 0, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_105);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_114);
lean_dec(x_108);
lean_dec(x_107);
lean_free_object(x_40);
lean_dec(x_7);
lean_dec(x_6);
x_152 = lean_box(1);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_105);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_107);
x_154 = lean_mk_string_unchecked("Failed to execute external prover:\n", 35, 35);
x_155 = lean_string_append(x_154, x_108);
lean_dec(x_108);
lean_ctor_set_tag(x_40, 3);
lean_ctor_set(x_40, 0, x_155);
x_156 = l_Lean_MessageData_ofFormat(x_40);
x_157 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_156, x_6, x_7, x_105);
lean_dec(x_7);
lean_dec(x_6);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint32_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint32_t x_165; uint8_t x_166; 
x_158 = lean_ctor_get(x_40, 0);
lean_inc(x_158);
lean_dec(x_40);
x_159 = lean_ctor_get(x_39, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_160 = x_39;
} else {
 lean_dec_ref(x_39);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get_uint32(x_158, sizeof(void*)*2);
x_162 = lean_ctor_get(x_158, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_158, 1);
lean_inc(x_163);
lean_dec(x_158);
x_164 = lean_unsigned_to_nat(255u);
x_165 = lean_uint32_of_nat(x_164);
x_166 = lean_uint32_dec_eq(x_161, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_167 = lean_mk_string_unchecked("s UNSATISFIABLE", 15, 15);
x_168 = lean_string_utf8_byte_size(x_162);
lean_inc(x_162);
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_162);
lean_ctor_set(x_169, 1, x_32);
lean_ctor_set(x_169, 2, x_168);
x_170 = lean_unsigned_to_nat(15u);
x_171 = l_Substring_nextn(x_169, x_170, x_32);
lean_inc(x_162);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_162);
lean_ctor_set(x_172, 1, x_32);
lean_ctor_set(x_172, 2, x_171);
x_173 = lean_string_utf8_byte_size(x_167);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_32);
lean_ctor_set(x_174, 2, x_173);
x_175 = l_Substring_beq(x_172, x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_176 = lean_mk_string_unchecked("s SATISFIABLE", 13, 13);
x_177 = lean_unsigned_to_nat(13u);
x_178 = l_Substring_nextn(x_169, x_177, x_32);
lean_dec(x_169);
lean_inc(x_162);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_162);
lean_ctor_set(x_179, 1, x_32);
lean_ctor_set(x_179, 2, x_178);
x_180 = lean_string_utf8_byte_size(x_176);
x_181 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_32);
lean_ctor_set(x_181, 2, x_180);
x_182 = l_Substring_beq(x_179, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_160);
x_183 = lean_mk_string_unchecked("The external prover produced unexpected output, stdout:\n", 56, 56);
x_184 = lean_string_append(x_183, x_162);
lean_dec(x_162);
x_185 = lean_mk_string_unchecked("stderr:\n", 8, 8);
x_186 = lean_string_append(x_184, x_185);
lean_dec(x_185);
x_187 = lean_string_append(x_186, x_163);
lean_dec(x_163);
x_188 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = l_Lean_MessageData_ofFormat(x_188);
x_190 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_189, x_6, x_7, x_159);
lean_dec(x_7);
lean_dec(x_6);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_163);
x_191 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_External_ModelParser_parse), 1, 0);
x_192 = lean_string_to_utf8(x_162);
x_193 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_191, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_160);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
x_196 = lean_mk_string_unchecked("Error ", 6, 6);
x_197 = lean_string_append(x_196, x_194);
lean_dec(x_194);
x_198 = lean_mk_string_unchecked(" while parsing:\n", 16, 16);
x_199 = lean_string_append(x_197, x_198);
lean_dec(x_198);
x_200 = lean_string_append(x_199, x_162);
lean_dec(x_162);
if (lean_is_scalar(x_195)) {
 x_201 = lean_alloc_ctor(3, 1, 0);
} else {
 x_201 = x_195;
 lean_ctor_set_tag(x_201, 3);
}
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Lean_MessageData_ofFormat(x_201);
x_203 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_202, x_6, x_7, x_159);
lean_dec(x_7);
lean_dec(x_6);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_162);
lean_dec(x_7);
lean_dec(x_6);
x_204 = lean_ctor_get(x_193, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_205 = x_193;
} else {
 lean_dec_ref(x_193);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 1, 0);
} else {
 x_206 = x_205;
 lean_ctor_set_tag(x_206, 0);
}
lean_ctor_set(x_206, 0, x_204);
if (lean_is_scalar(x_160)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_160;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_159);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_7);
lean_dec(x_6);
x_208 = lean_box(1);
if (lean_is_scalar(x_160)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_160;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_159);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_162);
lean_dec(x_160);
x_210 = lean_mk_string_unchecked("Failed to execute external prover:\n", 35, 35);
x_211 = lean_string_append(x_210, x_163);
lean_dec(x_163);
x_212 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l_Lean_MessageData_ofFormat(x_212);
x_214 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_213, x_6, x_7, x_159);
lean_dec(x_7);
lean_dec(x_6);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_39, 1);
lean_inc(x_215);
lean_dec(x_39);
x_216 = lean_mk_string_unchecked("The SAT solver timed out while solving the problem.\nConsider increasing the timeout with the `timeout` config option.\nIf solving your problem relies inherently on using associativity or commutativity, consider enabling the `acNf` config option.", 244, 244);
x_217 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_217, 0, x_216);
x_218 = l_Lean_MessageData_ofFormat(x_217);
x_219 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_218, x_6, x_7, x_215);
lean_dec(x_7);
lean_dec(x_6);
return x_219;
}
}
else
{
uint8_t x_220; 
lean_dec(x_7);
lean_dec(x_6);
x_220 = !lean_is_exclusive(x_39);
if (x_220 == 0)
{
return x_39;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_39, 0);
x_222 = lean_ctor_get(x_39, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_39);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Elab_Tactic_BVDecide_External_satQuery_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_External_satQuery___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Elab_Tactic_BVDecide_External_satQuery(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_External(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
