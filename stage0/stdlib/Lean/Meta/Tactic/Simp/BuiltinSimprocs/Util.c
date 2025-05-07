// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
// Imports: Lean.Meta.Tactic.Simp.Simproc
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkDecide(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(1);
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_mk_string_unchecked("Bool", 4, 4);
x_13 = lean_mk_string_unchecked("false", 5, 5);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_const___override(x_14, x_15);
x_17 = l_Lean_Meta_mkEqRefl(x_16, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_mk_string_unchecked("False", 5, 5);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Expr_const___override(x_21, x_15);
x_23 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = l_Lean_Expr_const___override(x_24, x_15);
x_26 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
x_29 = lean_array_push(x_28, x_1);
x_30 = lean_array_push(x_29, x_26);
x_31 = lean_array_push(x_30, x_19);
x_32 = l_Lean_mkAppN(x_25, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_unbox(x_11);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_35);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_17, 0, x_36);
return x_17;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_mk_string_unchecked("False", 5, 5);
x_40 = l_Lean_Name_mkStr1(x_39);
x_41 = l_Lean_Expr_const___override(x_40, x_15);
x_42 = lean_mk_string_unchecked("eq_false_of_decide", 18, 18);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = l_Lean_Expr_const___override(x_43, x_15);
x_45 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_mk_empty_array_with_capacity(x_46);
x_48 = lean_array_push(x_47, x_1);
x_49 = lean_array_push(x_48, x_45);
x_50 = lean_array_push(x_49, x_37);
x_51 = l_Lean_mkAppN(x_44, x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unbox(x_11);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_54);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_38);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
return x_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_mk_string_unchecked("Bool", 4, 4);
x_62 = lean_mk_string_unchecked("true", 4, 4);
x_63 = l_Lean_Name_mkStr2(x_61, x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Expr_const___override(x_63, x_64);
x_66 = l_Lean_Meta_mkEqRefl(x_65, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_mk_string_unchecked("True", 4, 4);
x_70 = l_Lean_Name_mkStr1(x_69);
x_71 = l_Lean_Expr_const___override(x_70, x_64);
x_72 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_73 = l_Lean_Name_mkStr1(x_72);
x_74 = l_Lean_Expr_const___override(x_73, x_64);
x_75 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_76 = lean_unsigned_to_nat(3u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
x_78 = lean_array_push(x_77, x_1);
x_79 = lean_array_push(x_78, x_75);
x_80 = lean_array_push(x_79, x_68);
x_81 = l_Lean_mkAppN(x_74, x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_unbox(x_11);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_84);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_66, 0, x_85);
return x_66;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_86 = lean_ctor_get(x_66, 0);
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_66);
x_88 = lean_mk_string_unchecked("True", 4, 4);
x_89 = l_Lean_Name_mkStr1(x_88);
x_90 = l_Lean_Expr_const___override(x_89, x_64);
x_91 = lean_mk_string_unchecked("eq_true_of_decide", 17, 17);
x_92 = l_Lean_Name_mkStr1(x_91);
x_93 = l_Lean_Expr_const___override(x_92, x_64);
x_94 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_mk_empty_array_with_capacity(x_95);
x_97 = lean_array_push(x_96, x_1);
x_98 = lean_array_push(x_97, x_94);
x_99 = lean_array_push(x_98, x_86);
x_100 = l_Lean_mkAppN(x_93, x_99);
lean_dec(x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_90);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_unbox(x_11);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_103);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_87);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_9);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_66);
if (x_106 == 0)
{
return x_66;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_66, 0);
x_108 = lean_ctor_get(x_66, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_66);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_8);
if (x_110 == 0)
{
return x_8;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_8, 0);
x_112 = lean_ctor_get(x_8, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_8);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_Simp_evalPropStep___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_Simp_evalPropStep(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
