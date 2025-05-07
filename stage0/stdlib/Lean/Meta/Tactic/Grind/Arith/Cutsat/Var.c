// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
// Imports: Lean.Meta.IntInstTesters Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_hashRoot_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isZero(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsCutsatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_hashRoot_spec__0(lean_box(0), x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_free_object(x_11);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_mk_string_unchecked("grind", 5, 5);
x_22 = lean_mk_string_unchecked("debug", 5, 5);
x_23 = lean_mk_string_unchecked("cutsat", 6, 6);
x_24 = lean_mk_string_unchecked("internalize", 11, 11);
x_25 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
lean_inc(x_25);
x_26 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_25, x_8, x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_133; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_133 = lean_unbox(x_28);
lean_dec(x_28);
if (x_133 == 0)
{
lean_free_object(x_26);
lean_dec(x_25);
lean_free_object(x_17);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_29;
goto block_132;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_134 = lean_mk_string_unchecked("", 0, 0);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
lean_inc(x_1);
x_136 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_135);
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_136);
lean_ctor_set(x_26, 0, x_135);
x_137 = lean_mk_string_unchecked(" ↦ #", 6, 4);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_138);
lean_ctor_set(x_17, 0, x_26);
lean_inc(x_31);
x_139 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Lean_MessageData_ofFormat(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_17);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_135);
x_144 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_25, x_143, x_6, x_7, x_8, x_9, x_29);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_145;
goto block_132;
}
block_132:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_41 = lean_st_ref_take(x_32, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 7);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_42, sizeof(void*)*16);
x_53 = lean_ctor_get(x_42, 8);
lean_inc(x_53);
x_54 = lean_ctor_get(x_42, 9);
lean_inc(x_54);
x_55 = lean_ctor_get(x_42, 10);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 11);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 12);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 13);
lean_inc(x_58);
x_59 = lean_ctor_get(x_42, 14);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_inc(x_1);
x_63 = l_Lean_PersistentArray_push___redArg(x_62, x_1);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_inc(x_31);
lean_inc(x_1);
x_65 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(x_64, x_1, x_31);
x_66 = lean_ctor_get(x_61, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 5);
lean_inc(x_69);
x_70 = lean_box(0);
x_71 = l_Lean_PersistentArray_push___redArg(x_69, x_70);
x_72 = lean_ctor_get(x_61, 6);
lean_inc(x_72);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_unsigned_to_nat(5u);
x_75 = lean_usize_of_nat(x_74);
x_76 = lean_usize_to_nat(x_75);
x_77 = lean_nat_pow(x_73, x_76);
lean_dec(x_76);
x_78 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_79 = lean_usize_to_nat(x_78);
x_80 = lean_mk_empty_array_with_capacity(x_79);
lean_dec(x_79);
lean_inc(x_80);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_unsigned_to_nat(0u);
lean_inc(x_80);
x_83 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set_usize(x_83, 4, x_75);
lean_inc(x_83);
x_84 = l_Lean_PersistentArray_push___redArg(x_72, x_83);
x_85 = lean_ctor_get(x_61, 7);
lean_inc(x_85);
x_86 = l_Lean_PersistentArray_push___redArg(x_85, x_83);
x_87 = lean_ctor_get(x_61, 8);
lean_inc(x_87);
lean_inc(x_80);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_80);
x_89 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_82);
lean_ctor_set(x_89, 3, x_82);
lean_ctor_set_usize(x_89, 4, x_75);
x_90 = l_Lean_PersistentArray_push___redArg(x_87, x_89);
x_91 = lean_ctor_get(x_61, 9);
lean_inc(x_91);
x_92 = lean_box(0);
x_93 = l_Lean_PersistentArray_push___redArg(x_91, x_92);
x_94 = lean_ctor_get(x_61, 10);
lean_inc(x_94);
x_95 = lean_ctor_get(x_61, 11);
lean_inc(x_95);
x_96 = lean_box(0);
x_97 = l_Lean_PersistentArray_push___redArg(x_95, x_96);
x_98 = lean_ctor_get(x_61, 12);
lean_inc(x_98);
x_99 = lean_ctor_get(x_61, 13);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_61, sizeof(void*)*17);
x_101 = lean_ctor_get(x_61, 14);
lean_inc(x_101);
x_102 = lean_ctor_get(x_61, 15);
lean_inc(x_102);
x_103 = lean_ctor_get(x_61, 16);
lean_inc(x_103);
lean_dec(x_61);
x_104 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_104, 0, x_63);
lean_ctor_set(x_104, 1, x_65);
lean_ctor_set(x_104, 2, x_66);
lean_ctor_set(x_104, 3, x_67);
lean_ctor_set(x_104, 4, x_68);
lean_ctor_set(x_104, 5, x_71);
lean_ctor_set(x_104, 6, x_84);
lean_ctor_set(x_104, 7, x_86);
lean_ctor_set(x_104, 8, x_90);
lean_ctor_set(x_104, 9, x_93);
lean_ctor_set(x_104, 10, x_94);
lean_ctor_set(x_104, 11, x_97);
lean_ctor_set(x_104, 12, x_98);
lean_ctor_set(x_104, 13, x_99);
lean_ctor_set(x_104, 14, x_101);
lean_ctor_set(x_104, 15, x_102);
lean_ctor_set(x_104, 16, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*17, x_100);
x_105 = lean_ctor_get(x_59, 2);
lean_inc(x_105);
lean_dec(x_59);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_60);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_105);
x_107 = lean_ctor_get(x_42, 15);
lean_inc(x_107);
lean_dec(x_42);
x_108 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_108, 0, x_44);
lean_ctor_set(x_108, 1, x_45);
lean_ctor_set(x_108, 2, x_46);
lean_ctor_set(x_108, 3, x_47);
lean_ctor_set(x_108, 4, x_48);
lean_ctor_set(x_108, 5, x_49);
lean_ctor_set(x_108, 6, x_50);
lean_ctor_set(x_108, 7, x_51);
lean_ctor_set(x_108, 8, x_53);
lean_ctor_set(x_108, 9, x_54);
lean_ctor_set(x_108, 10, x_55);
lean_ctor_set(x_108, 11, x_56);
lean_ctor_set(x_108, 12, x_57);
lean_ctor_set(x_108, 13, x_58);
lean_ctor_set(x_108, 14, x_106);
lean_ctor_set(x_108, 15, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*16, x_52);
x_109 = lean_st_ref_set(x_32, x_108, x_43);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_1);
x_111 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_1);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_114);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_31);
return x_115;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_31);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_31);
x_120 = !lean_is_exclusive(x_115);
if (x_120 == 0)
{
return x_115;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_115, 0);
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_115);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_113);
if (x_124 == 0)
{
return x_113;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_113, 0);
x_126 = lean_ctor_get(x_113, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_113);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_111);
if (x_128 == 0)
{
return x_111;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_111, 0);
x_130 = lean_ctor_get(x_111, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_111);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_250; 
x_146 = lean_ctor_get(x_26, 0);
x_147 = lean_ctor_get(x_26, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_26);
x_148 = lean_ctor_get(x_19, 0);
lean_inc(x_148);
lean_dec(x_19);
x_149 = lean_ctor_get(x_148, 2);
lean_inc(x_149);
lean_dec(x_148);
x_250 = lean_unbox(x_146);
lean_dec(x_146);
if (x_250 == 0)
{
lean_dec(x_25);
lean_free_object(x_17);
x_150 = x_2;
x_151 = x_3;
x_152 = x_4;
x_153 = x_5;
x_154 = x_6;
x_155 = x_7;
x_156 = x_8;
x_157 = x_9;
x_158 = x_147;
goto block_249;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_251 = lean_mk_string_unchecked("", 0, 0);
x_252 = l_Lean_stringToMessageData(x_251);
lean_dec(x_251);
lean_inc(x_1);
x_253 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_252);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_mk_string_unchecked(" ↦ #", 6, 4);
x_256 = l_Lean_stringToMessageData(x_255);
lean_dec(x_255);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_256);
lean_ctor_set(x_17, 0, x_254);
lean_inc(x_149);
x_257 = l___private_Init_Data_Repr_0__Nat_reprFast(x_149);
x_258 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = l_Lean_MessageData_ofFormat(x_258);
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_17);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
x_262 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_25, x_261, x_6, x_7, x_8, x_9, x_147);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_150 = x_2;
x_151 = x_3;
x_152 = x_4;
x_153 = x_5;
x_154 = x_6;
x_155 = x_7;
x_156 = x_8;
x_157 = x_9;
x_158 = x_263;
goto block_249;
}
block_249:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; size_t x_193; lean_object* x_194; lean_object* x_195; size_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_159 = lean_st_ref_take(x_150, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 5);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 6);
lean_inc(x_168);
x_169 = lean_ctor_get(x_160, 7);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_160, sizeof(void*)*16);
x_171 = lean_ctor_get(x_160, 8);
lean_inc(x_171);
x_172 = lean_ctor_get(x_160, 9);
lean_inc(x_172);
x_173 = lean_ctor_get(x_160, 10);
lean_inc(x_173);
x_174 = lean_ctor_get(x_160, 11);
lean_inc(x_174);
x_175 = lean_ctor_get(x_160, 12);
lean_inc(x_175);
x_176 = lean_ctor_get(x_160, 13);
lean_inc(x_176);
x_177 = lean_ctor_get(x_160, 14);
lean_inc(x_177);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_inc(x_1);
x_181 = l_Lean_PersistentArray_push___redArg(x_180, x_1);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_inc(x_149);
lean_inc(x_1);
x_183 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(x_182, x_1, x_149);
x_184 = lean_ctor_get(x_179, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_179, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_179, 4);
lean_inc(x_186);
x_187 = lean_ctor_get(x_179, 5);
lean_inc(x_187);
x_188 = lean_box(0);
x_189 = l_Lean_PersistentArray_push___redArg(x_187, x_188);
x_190 = lean_ctor_get(x_179, 6);
lean_inc(x_190);
x_191 = lean_unsigned_to_nat(2u);
x_192 = lean_unsigned_to_nat(5u);
x_193 = lean_usize_of_nat(x_192);
x_194 = lean_usize_to_nat(x_193);
x_195 = lean_nat_pow(x_191, x_194);
lean_dec(x_194);
x_196 = lean_usize_of_nat(x_195);
lean_dec(x_195);
x_197 = lean_usize_to_nat(x_196);
x_198 = lean_mk_empty_array_with_capacity(x_197);
lean_dec(x_197);
lean_inc(x_198);
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = lean_unsigned_to_nat(0u);
lean_inc(x_198);
x_201 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_198);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set_usize(x_201, 4, x_193);
lean_inc(x_201);
x_202 = l_Lean_PersistentArray_push___redArg(x_190, x_201);
x_203 = lean_ctor_get(x_179, 7);
lean_inc(x_203);
x_204 = l_Lean_PersistentArray_push___redArg(x_203, x_201);
x_205 = lean_ctor_get(x_179, 8);
lean_inc(x_205);
lean_inc(x_198);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_198);
x_207 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_198);
lean_ctor_set(x_207, 2, x_200);
lean_ctor_set(x_207, 3, x_200);
lean_ctor_set_usize(x_207, 4, x_193);
x_208 = l_Lean_PersistentArray_push___redArg(x_205, x_207);
x_209 = lean_ctor_get(x_179, 9);
lean_inc(x_209);
x_210 = lean_box(0);
x_211 = l_Lean_PersistentArray_push___redArg(x_209, x_210);
x_212 = lean_ctor_get(x_179, 10);
lean_inc(x_212);
x_213 = lean_ctor_get(x_179, 11);
lean_inc(x_213);
x_214 = lean_box(0);
x_215 = l_Lean_PersistentArray_push___redArg(x_213, x_214);
x_216 = lean_ctor_get(x_179, 12);
lean_inc(x_216);
x_217 = lean_ctor_get(x_179, 13);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_179, sizeof(void*)*17);
x_219 = lean_ctor_get(x_179, 14);
lean_inc(x_219);
x_220 = lean_ctor_get(x_179, 15);
lean_inc(x_220);
x_221 = lean_ctor_get(x_179, 16);
lean_inc(x_221);
lean_dec(x_179);
x_222 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_222, 0, x_181);
lean_ctor_set(x_222, 1, x_183);
lean_ctor_set(x_222, 2, x_184);
lean_ctor_set(x_222, 3, x_185);
lean_ctor_set(x_222, 4, x_186);
lean_ctor_set(x_222, 5, x_189);
lean_ctor_set(x_222, 6, x_202);
lean_ctor_set(x_222, 7, x_204);
lean_ctor_set(x_222, 8, x_208);
lean_ctor_set(x_222, 9, x_211);
lean_ctor_set(x_222, 10, x_212);
lean_ctor_set(x_222, 11, x_215);
lean_ctor_set(x_222, 12, x_216);
lean_ctor_set(x_222, 13, x_217);
lean_ctor_set(x_222, 14, x_219);
lean_ctor_set(x_222, 15, x_220);
lean_ctor_set(x_222, 16, x_221);
lean_ctor_set_uint8(x_222, sizeof(void*)*17, x_218);
x_223 = lean_ctor_get(x_177, 2);
lean_inc(x_223);
lean_dec(x_177);
x_224 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_224, 0, x_178);
lean_ctor_set(x_224, 1, x_222);
lean_ctor_set(x_224, 2, x_223);
x_225 = lean_ctor_get(x_160, 15);
lean_inc(x_225);
lean_dec(x_160);
x_226 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_226, 0, x_162);
lean_ctor_set(x_226, 1, x_163);
lean_ctor_set(x_226, 2, x_164);
lean_ctor_set(x_226, 3, x_165);
lean_ctor_set(x_226, 4, x_166);
lean_ctor_set(x_226, 5, x_167);
lean_ctor_set(x_226, 6, x_168);
lean_ctor_set(x_226, 7, x_169);
lean_ctor_set(x_226, 8, x_171);
lean_ctor_set(x_226, 9, x_172);
lean_ctor_set(x_226, 10, x_173);
lean_ctor_set(x_226, 11, x_174);
lean_ctor_set(x_226, 12, x_175);
lean_ctor_set(x_226, 13, x_176);
lean_ctor_set(x_226, 14, x_224);
lean_ctor_set(x_226, 15, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*16, x_170);
x_227 = lean_st_ref_set(x_150, x_226, x_161);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_1);
x_229 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_1);
x_231 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_149, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_233 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_149);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_149);
x_237 = lean_ctor_get(x_233, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_239 = x_233;
} else {
 lean_dec_ref(x_233);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_1);
x_241 = lean_ctor_get(x_231, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_231, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_243 = x_231;
} else {
 lean_dec_ref(x_231);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_1);
x_245 = lean_ctor_get(x_229, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_229, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_247 = x_229;
} else {
 lean_dec_ref(x_229);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_377; 
x_264 = lean_ctor_get(x_17, 0);
x_265 = lean_ctor_get(x_17, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_17);
x_266 = lean_mk_string_unchecked("grind", 5, 5);
x_267 = lean_mk_string_unchecked("debug", 5, 5);
x_268 = lean_mk_string_unchecked("cutsat", 6, 6);
x_269 = lean_mk_string_unchecked("internalize", 11, 11);
x_270 = l_Lean_Name_mkStr4(x_266, x_267, x_268, x_269);
lean_inc(x_270);
x_271 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_270, x_8, x_265);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
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
x_275 = lean_ctor_get(x_264, 0);
lean_inc(x_275);
lean_dec(x_264);
x_276 = lean_ctor_get(x_275, 2);
lean_inc(x_276);
lean_dec(x_275);
x_377 = lean_unbox(x_272);
lean_dec(x_272);
if (x_377 == 0)
{
lean_dec(x_274);
lean_dec(x_270);
x_277 = x_2;
x_278 = x_3;
x_279 = x_4;
x_280 = x_5;
x_281 = x_6;
x_282 = x_7;
x_283 = x_8;
x_284 = x_9;
x_285 = x_273;
goto block_376;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_378 = lean_mk_string_unchecked("", 0, 0);
x_379 = l_Lean_stringToMessageData(x_378);
lean_dec(x_378);
lean_inc(x_1);
x_380 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_379);
if (lean_is_scalar(x_274)) {
 x_381 = lean_alloc_ctor(7, 2, 0);
} else {
 x_381 = x_274;
 lean_ctor_set_tag(x_381, 7);
}
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_mk_string_unchecked(" ↦ #", 6, 4);
x_383 = l_Lean_stringToMessageData(x_382);
lean_dec(x_382);
x_384 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_383);
lean_inc(x_276);
x_385 = l___private_Init_Data_Repr_0__Nat_reprFast(x_276);
x_386 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_386, 0, x_385);
x_387 = l_Lean_MessageData_ofFormat(x_386);
x_388 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_388, 0, x_384);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_379);
x_390 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_270, x_389, x_6, x_7, x_8, x_9, x_273);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_277 = x_2;
x_278 = x_3;
x_279 = x_4;
x_280 = x_5;
x_281 = x_6;
x_282 = x_7;
x_283 = x_8;
x_284 = x_9;
x_285 = x_391;
goto block_376;
}
block_376:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; size_t x_320; lean_object* x_321; lean_object* x_322; size_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_286 = lean_st_ref_take(x_277, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_287, 2);
lean_inc(x_291);
x_292 = lean_ctor_get(x_287, 3);
lean_inc(x_292);
x_293 = lean_ctor_get(x_287, 4);
lean_inc(x_293);
x_294 = lean_ctor_get(x_287, 5);
lean_inc(x_294);
x_295 = lean_ctor_get(x_287, 6);
lean_inc(x_295);
x_296 = lean_ctor_get(x_287, 7);
lean_inc(x_296);
x_297 = lean_ctor_get_uint8(x_287, sizeof(void*)*16);
x_298 = lean_ctor_get(x_287, 8);
lean_inc(x_298);
x_299 = lean_ctor_get(x_287, 9);
lean_inc(x_299);
x_300 = lean_ctor_get(x_287, 10);
lean_inc(x_300);
x_301 = lean_ctor_get(x_287, 11);
lean_inc(x_301);
x_302 = lean_ctor_get(x_287, 12);
lean_inc(x_302);
x_303 = lean_ctor_get(x_287, 13);
lean_inc(x_303);
x_304 = lean_ctor_get(x_287, 14);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
lean_inc(x_1);
x_308 = l_Lean_PersistentArray_push___redArg(x_307, x_1);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_inc(x_276);
lean_inc(x_1);
x_310 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(x_309, x_1, x_276);
x_311 = lean_ctor_get(x_306, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_306, 3);
lean_inc(x_312);
x_313 = lean_ctor_get(x_306, 4);
lean_inc(x_313);
x_314 = lean_ctor_get(x_306, 5);
lean_inc(x_314);
x_315 = lean_box(0);
x_316 = l_Lean_PersistentArray_push___redArg(x_314, x_315);
x_317 = lean_ctor_get(x_306, 6);
lean_inc(x_317);
x_318 = lean_unsigned_to_nat(2u);
x_319 = lean_unsigned_to_nat(5u);
x_320 = lean_usize_of_nat(x_319);
x_321 = lean_usize_to_nat(x_320);
x_322 = lean_nat_pow(x_318, x_321);
lean_dec(x_321);
x_323 = lean_usize_of_nat(x_322);
lean_dec(x_322);
x_324 = lean_usize_to_nat(x_323);
x_325 = lean_mk_empty_array_with_capacity(x_324);
lean_dec(x_324);
lean_inc(x_325);
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_unsigned_to_nat(0u);
lean_inc(x_325);
x_328 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_325);
lean_ctor_set(x_328, 2, x_327);
lean_ctor_set(x_328, 3, x_327);
lean_ctor_set_usize(x_328, 4, x_320);
lean_inc(x_328);
x_329 = l_Lean_PersistentArray_push___redArg(x_317, x_328);
x_330 = lean_ctor_get(x_306, 7);
lean_inc(x_330);
x_331 = l_Lean_PersistentArray_push___redArg(x_330, x_328);
x_332 = lean_ctor_get(x_306, 8);
lean_inc(x_332);
lean_inc(x_325);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_325);
x_334 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_325);
lean_ctor_set(x_334, 2, x_327);
lean_ctor_set(x_334, 3, x_327);
lean_ctor_set_usize(x_334, 4, x_320);
x_335 = l_Lean_PersistentArray_push___redArg(x_332, x_334);
x_336 = lean_ctor_get(x_306, 9);
lean_inc(x_336);
x_337 = lean_box(0);
x_338 = l_Lean_PersistentArray_push___redArg(x_336, x_337);
x_339 = lean_ctor_get(x_306, 10);
lean_inc(x_339);
x_340 = lean_ctor_get(x_306, 11);
lean_inc(x_340);
x_341 = lean_box(0);
x_342 = l_Lean_PersistentArray_push___redArg(x_340, x_341);
x_343 = lean_ctor_get(x_306, 12);
lean_inc(x_343);
x_344 = lean_ctor_get(x_306, 13);
lean_inc(x_344);
x_345 = lean_ctor_get_uint8(x_306, sizeof(void*)*17);
x_346 = lean_ctor_get(x_306, 14);
lean_inc(x_346);
x_347 = lean_ctor_get(x_306, 15);
lean_inc(x_347);
x_348 = lean_ctor_get(x_306, 16);
lean_inc(x_348);
lean_dec(x_306);
x_349 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_349, 0, x_308);
lean_ctor_set(x_349, 1, x_310);
lean_ctor_set(x_349, 2, x_311);
lean_ctor_set(x_349, 3, x_312);
lean_ctor_set(x_349, 4, x_313);
lean_ctor_set(x_349, 5, x_316);
lean_ctor_set(x_349, 6, x_329);
lean_ctor_set(x_349, 7, x_331);
lean_ctor_set(x_349, 8, x_335);
lean_ctor_set(x_349, 9, x_338);
lean_ctor_set(x_349, 10, x_339);
lean_ctor_set(x_349, 11, x_342);
lean_ctor_set(x_349, 12, x_343);
lean_ctor_set(x_349, 13, x_344);
lean_ctor_set(x_349, 14, x_346);
lean_ctor_set(x_349, 15, x_347);
lean_ctor_set(x_349, 16, x_348);
lean_ctor_set_uint8(x_349, sizeof(void*)*17, x_345);
x_350 = lean_ctor_get(x_304, 2);
lean_inc(x_350);
lean_dec(x_304);
x_351 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_351, 0, x_305);
lean_ctor_set(x_351, 1, x_349);
lean_ctor_set(x_351, 2, x_350);
x_352 = lean_ctor_get(x_287, 15);
lean_inc(x_352);
lean_dec(x_287);
x_353 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_353, 0, x_289);
lean_ctor_set(x_353, 1, x_290);
lean_ctor_set(x_353, 2, x_291);
lean_ctor_set(x_353, 3, x_292);
lean_ctor_set(x_353, 4, x_293);
lean_ctor_set(x_353, 5, x_294);
lean_ctor_set(x_353, 6, x_295);
lean_ctor_set(x_353, 7, x_296);
lean_ctor_set(x_353, 8, x_298);
lean_ctor_set(x_353, 9, x_299);
lean_ctor_set(x_353, 10, x_300);
lean_ctor_set(x_353, 11, x_301);
lean_ctor_set(x_353, 12, x_302);
lean_ctor_set(x_353, 13, x_303);
lean_ctor_set(x_353, 14, x_351);
lean_ctor_set(x_353, 15, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*16, x_297);
x_354 = lean_st_ref_set(x_277, x_353, x_288);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_1);
x_356 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec(x_356);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_1);
x_358 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_276, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec(x_358);
x_360 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_277, x_278, x_279, x_280, x_281, x_282, x_283, x_284, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_360, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_362 = x_360;
} else {
 lean_dec_ref(x_360);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_276);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_276);
x_364 = lean_ctor_get(x_360, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_360, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_366 = x_360;
} else {
 lean_dec_ref(x_360);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_1);
x_368 = lean_ctor_get(x_358, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_358, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_370 = x_358;
} else {
 lean_dec_ref(x_358);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_1);
x_372 = lean_ctor_get(x_356, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_356, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_374 = x_356;
} else {
 lean_dec_ref(x_356);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
}
}
else
{
lean_object* x_392; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_392 = lean_ctor_get(x_16, 0);
lean_inc(x_392);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_392);
return x_11;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = lean_ctor_get(x_11, 0);
x_394 = lean_ctor_get(x_11, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_11);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_hashRoot_spec__0(lean_box(0), x_395, x_1);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_512; 
x_397 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_394);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
x_401 = lean_mk_string_unchecked("grind", 5, 5);
x_402 = lean_mk_string_unchecked("debug", 5, 5);
x_403 = lean_mk_string_unchecked("cutsat", 6, 6);
x_404 = lean_mk_string_unchecked("internalize", 11, 11);
x_405 = l_Lean_Name_mkStr4(x_401, x_402, x_403, x_404);
lean_inc(x_405);
x_406 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_405, x_8, x_399);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_409 = x_406;
} else {
 lean_dec_ref(x_406);
 x_409 = lean_box(0);
}
x_410 = lean_ctor_get(x_398, 0);
lean_inc(x_410);
lean_dec(x_398);
x_411 = lean_ctor_get(x_410, 2);
lean_inc(x_411);
lean_dec(x_410);
x_512 = lean_unbox(x_407);
lean_dec(x_407);
if (x_512 == 0)
{
lean_dec(x_409);
lean_dec(x_405);
lean_dec(x_400);
x_412 = x_2;
x_413 = x_3;
x_414 = x_4;
x_415 = x_5;
x_416 = x_6;
x_417 = x_7;
x_418 = x_8;
x_419 = x_9;
x_420 = x_408;
goto block_511;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_513 = lean_mk_string_unchecked("", 0, 0);
x_514 = l_Lean_stringToMessageData(x_513);
lean_dec(x_513);
lean_inc(x_1);
x_515 = l_Lean_MessageData_ofExpr(x_1);
lean_inc(x_514);
if (lean_is_scalar(x_409)) {
 x_516 = lean_alloc_ctor(7, 2, 0);
} else {
 x_516 = x_409;
 lean_ctor_set_tag(x_516, 7);
}
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
x_517 = lean_mk_string_unchecked(" ↦ #", 6, 4);
x_518 = l_Lean_stringToMessageData(x_517);
lean_dec(x_517);
if (lean_is_scalar(x_400)) {
 x_519 = lean_alloc_ctor(7, 2, 0);
} else {
 x_519 = x_400;
 lean_ctor_set_tag(x_519, 7);
}
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_518);
lean_inc(x_411);
x_520 = l___private_Init_Data_Repr_0__Nat_reprFast(x_411);
x_521 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_521, 0, x_520);
x_522 = l_Lean_MessageData_ofFormat(x_521);
x_523 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_523, 0, x_519);
lean_ctor_set(x_523, 1, x_522);
x_524 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_514);
x_525 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_405, x_524, x_6, x_7, x_8, x_9, x_408);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
lean_dec(x_525);
x_412 = x_2;
x_413 = x_3;
x_414 = x_4;
x_415 = x_5;
x_416 = x_6;
x_417 = x_7;
x_418 = x_8;
x_419 = x_9;
x_420 = x_526;
goto block_511;
}
block_511:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; size_t x_455; lean_object* x_456; lean_object* x_457; size_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_421 = lean_st_ref_take(x_412, x_420);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_422, 2);
lean_inc(x_426);
x_427 = lean_ctor_get(x_422, 3);
lean_inc(x_427);
x_428 = lean_ctor_get(x_422, 4);
lean_inc(x_428);
x_429 = lean_ctor_get(x_422, 5);
lean_inc(x_429);
x_430 = lean_ctor_get(x_422, 6);
lean_inc(x_430);
x_431 = lean_ctor_get(x_422, 7);
lean_inc(x_431);
x_432 = lean_ctor_get_uint8(x_422, sizeof(void*)*16);
x_433 = lean_ctor_get(x_422, 8);
lean_inc(x_433);
x_434 = lean_ctor_get(x_422, 9);
lean_inc(x_434);
x_435 = lean_ctor_get(x_422, 10);
lean_inc(x_435);
x_436 = lean_ctor_get(x_422, 11);
lean_inc(x_436);
x_437 = lean_ctor_get(x_422, 12);
lean_inc(x_437);
x_438 = lean_ctor_get(x_422, 13);
lean_inc(x_438);
x_439 = lean_ctor_get(x_422, 14);
lean_inc(x_439);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
lean_inc(x_1);
x_443 = l_Lean_PersistentArray_push___redArg(x_442, x_1);
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_inc(x_411);
lean_inc(x_1);
x_445 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(x_444, x_1, x_411);
x_446 = lean_ctor_get(x_441, 2);
lean_inc(x_446);
x_447 = lean_ctor_get(x_441, 3);
lean_inc(x_447);
x_448 = lean_ctor_get(x_441, 4);
lean_inc(x_448);
x_449 = lean_ctor_get(x_441, 5);
lean_inc(x_449);
x_450 = lean_box(0);
x_451 = l_Lean_PersistentArray_push___redArg(x_449, x_450);
x_452 = lean_ctor_get(x_441, 6);
lean_inc(x_452);
x_453 = lean_unsigned_to_nat(2u);
x_454 = lean_unsigned_to_nat(5u);
x_455 = lean_usize_of_nat(x_454);
x_456 = lean_usize_to_nat(x_455);
x_457 = lean_nat_pow(x_453, x_456);
lean_dec(x_456);
x_458 = lean_usize_of_nat(x_457);
lean_dec(x_457);
x_459 = lean_usize_to_nat(x_458);
x_460 = lean_mk_empty_array_with_capacity(x_459);
lean_dec(x_459);
lean_inc(x_460);
x_461 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_461, 0, x_460);
x_462 = lean_unsigned_to_nat(0u);
lean_inc(x_460);
x_463 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_460);
lean_ctor_set(x_463, 2, x_462);
lean_ctor_set(x_463, 3, x_462);
lean_ctor_set_usize(x_463, 4, x_455);
lean_inc(x_463);
x_464 = l_Lean_PersistentArray_push___redArg(x_452, x_463);
x_465 = lean_ctor_get(x_441, 7);
lean_inc(x_465);
x_466 = l_Lean_PersistentArray_push___redArg(x_465, x_463);
x_467 = lean_ctor_get(x_441, 8);
lean_inc(x_467);
lean_inc(x_460);
x_468 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_468, 0, x_460);
x_469 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_460);
lean_ctor_set(x_469, 2, x_462);
lean_ctor_set(x_469, 3, x_462);
lean_ctor_set_usize(x_469, 4, x_455);
x_470 = l_Lean_PersistentArray_push___redArg(x_467, x_469);
x_471 = lean_ctor_get(x_441, 9);
lean_inc(x_471);
x_472 = lean_box(0);
x_473 = l_Lean_PersistentArray_push___redArg(x_471, x_472);
x_474 = lean_ctor_get(x_441, 10);
lean_inc(x_474);
x_475 = lean_ctor_get(x_441, 11);
lean_inc(x_475);
x_476 = lean_box(0);
x_477 = l_Lean_PersistentArray_push___redArg(x_475, x_476);
x_478 = lean_ctor_get(x_441, 12);
lean_inc(x_478);
x_479 = lean_ctor_get(x_441, 13);
lean_inc(x_479);
x_480 = lean_ctor_get_uint8(x_441, sizeof(void*)*17);
x_481 = lean_ctor_get(x_441, 14);
lean_inc(x_481);
x_482 = lean_ctor_get(x_441, 15);
lean_inc(x_482);
x_483 = lean_ctor_get(x_441, 16);
lean_inc(x_483);
lean_dec(x_441);
x_484 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_484, 0, x_443);
lean_ctor_set(x_484, 1, x_445);
lean_ctor_set(x_484, 2, x_446);
lean_ctor_set(x_484, 3, x_447);
lean_ctor_set(x_484, 4, x_448);
lean_ctor_set(x_484, 5, x_451);
lean_ctor_set(x_484, 6, x_464);
lean_ctor_set(x_484, 7, x_466);
lean_ctor_set(x_484, 8, x_470);
lean_ctor_set(x_484, 9, x_473);
lean_ctor_set(x_484, 10, x_474);
lean_ctor_set(x_484, 11, x_477);
lean_ctor_set(x_484, 12, x_478);
lean_ctor_set(x_484, 13, x_479);
lean_ctor_set(x_484, 14, x_481);
lean_ctor_set(x_484, 15, x_482);
lean_ctor_set(x_484, 16, x_483);
lean_ctor_set_uint8(x_484, sizeof(void*)*17, x_480);
x_485 = lean_ctor_get(x_439, 2);
lean_inc(x_485);
lean_dec(x_439);
x_486 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_486, 0, x_440);
lean_ctor_set(x_486, 1, x_484);
lean_ctor_set(x_486, 2, x_485);
x_487 = lean_ctor_get(x_422, 15);
lean_inc(x_487);
lean_dec(x_422);
x_488 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_488, 0, x_424);
lean_ctor_set(x_488, 1, x_425);
lean_ctor_set(x_488, 2, x_426);
lean_ctor_set(x_488, 3, x_427);
lean_ctor_set(x_488, 4, x_428);
lean_ctor_set(x_488, 5, x_429);
lean_ctor_set(x_488, 6, x_430);
lean_ctor_set(x_488, 7, x_431);
lean_ctor_set(x_488, 8, x_433);
lean_ctor_set(x_488, 9, x_434);
lean_ctor_set(x_488, 10, x_435);
lean_ctor_set(x_488, 11, x_436);
lean_ctor_set(x_488, 12, x_437);
lean_ctor_set(x_488, 13, x_438);
lean_ctor_set(x_488, 14, x_486);
lean_ctor_set(x_488, 15, x_487);
lean_ctor_set_uint8(x_488, sizeof(void*)*16, x_432);
x_489 = lean_st_ref_set(x_412, x_488, x_423);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
lean_dec(x_489);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_1);
x_491 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_412, x_413, x_414, x_415, x_416, x_417, x_418, x_419, x_490);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
lean_dec(x_491);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_1);
x_493 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_411, x_412, x_413, x_414, x_415, x_416, x_417, x_418, x_419, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_495 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_412, x_413, x_414, x_415, x_416, x_417, x_418, x_419, x_494);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_497 = x_495;
} else {
 lean_dec_ref(x_495);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_411);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_411);
x_499 = lean_ctor_get(x_495, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_495, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_501 = x_495;
} else {
 lean_dec_ref(x_495);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_500);
return x_502;
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_1);
x_503 = lean_ctor_get(x_493, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_493, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_505 = x_493;
} else {
 lean_dec_ref(x_493);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_503);
lean_ctor_set(x_506, 1, x_504);
return x_506;
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_1);
x_507 = lean_ctor_get(x_491, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_491, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_509 = x_491;
} else {
 lean_dec_ref(x_491);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
}
else
{
lean_object* x_527; lean_object* x_528; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_527 = lean_ctor_get(x_396, 0);
lean_inc(x_527);
lean_dec(x_396);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_394);
return x_528;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("Int", 3, 3);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_11, x_12);
x_14 = l_Lean_Meta_isExprDefEq(x_8, x_13, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_2);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isInt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_22 = l_Lean_Expr_cleanupAnnotations(x_16);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_inc(x_24);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_inc(x_26);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = lean_mk_string_unchecked("HAdd", 4, 4);
x_36 = lean_mk_string_unchecked("hAdd", 4, 4);
x_37 = l_Lean_Name_mkStr2(x_35, x_36);
x_38 = l_Lean_Expr_isConstOf(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
if (x_38 == 0)
{
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_18);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_dec(x_26);
x_40 = l_Lean_Meta_isInstHAddInt___redArg(x_39, x_7, x_17);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
if (x_2 == 0)
{
lean_object* x_43; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_11 = x_43;
goto block_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*7 + 10);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_11 = x_48;
goto block_14;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_45, 1);
x_51 = lean_ctor_get(x_45, 0);
lean_dec(x_51);
x_52 = lean_mk_string_unchecked("found term with non-standard instance", 37, 37);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_54);
lean_ctor_set(x_45, 0, x_53);
x_55 = lean_mk_string_unchecked("", 0, 0);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_Grind_reportIssue(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_11 = x_59;
goto block_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_mk_string_unchecked("found term with non-standard instance", 37, 37);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = l_Lean_indentExpr(x_1);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("", 0, 0);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_Grind_reportIssue(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_60);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_11 = x_69;
goto block_14;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_40);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_40, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_22, 1);
lean_inc(x_72);
lean_dec(x_22);
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
lean_dec(x_24);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_40, 0, x_75);
return x_40;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_40, 1);
lean_inc(x_76);
lean_dec(x_40);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
lean_dec(x_22);
x_78 = lean_ctor_get(x_24, 1);
lean_inc(x_78);
lean_dec(x_24);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(1);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_22 = l_Lean_Expr_cleanupAnnotations(x_16);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_inc(x_24);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_inc(x_26);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_32);
x_35 = lean_mk_string_unchecked("HMul", 4, 4);
x_36 = lean_mk_string_unchecked("hMul", 4, 4);
x_37 = l_Lean_Name_mkStr2(x_35, x_36);
x_38 = l_Lean_Expr_isConstOf(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
if (x_38 == 0)
{
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_18);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_dec(x_26);
x_40 = l_Lean_Meta_isInstHMulInt___redArg(x_39, x_7, x_17);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
if (x_2 == 0)
{
lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_11 = x_43;
goto block_14;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_40, 1);
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
x_47 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*7 + 10);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_free_object(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_11 = x_50;
goto block_14;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_47, 1);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = lean_mk_string_unchecked("found term with non-standard instance", 37, 37);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_56);
lean_ctor_set(x_47, 0, x_55);
x_57 = lean_mk_string_unchecked("", 0, 0);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_58);
lean_ctor_set(x_40, 0, x_47);
x_59 = l_Lean_Meta_Grind_reportIssue(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_11 = x_60;
goto block_14;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_dec(x_47);
x_62 = lean_mk_string_unchecked("found term with non-standard instance", 37, 37);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = l_Lean_indentExpr(x_1);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked("", 0, 0);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_67);
lean_ctor_set(x_40, 0, x_65);
x_68 = l_Lean_Meta_Grind_reportIssue(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_11 = x_69;
goto block_14;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_dec(x_40);
x_71 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*7 + 10);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_11 = x_74;
goto block_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
x_77 = lean_mk_string_unchecked("found term with non-standard instance", 37, 37);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_76)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_76;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_Grind_reportIssue(x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_11 = x_85;
goto block_14;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_40);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_40, 1);
x_88 = lean_ctor_get(x_40, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_24, 1);
lean_inc(x_89);
lean_dec(x_24);
x_90 = l_Lean_Meta_getIntValue_x3f(x_89, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
lean_free_object(x_40);
lean_dec(x_22);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set(x_90, 0, x_94);
return x_90;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_90);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_90, 0);
lean_dec(x_99);
x_100 = !lean_is_exclusive(x_91);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_91, 0);
x_102 = lean_ctor_get(x_22, 1);
lean_inc(x_102);
lean_dec(x_22);
lean_ctor_set(x_40, 1, x_102);
lean_ctor_set(x_40, 0, x_101);
lean_ctor_set(x_91, 0, x_40);
return x_90;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
lean_dec(x_91);
x_104 = lean_ctor_get(x_22, 1);
lean_inc(x_104);
lean_dec(x_22);
lean_ctor_set(x_40, 1, x_104);
lean_ctor_set(x_40, 0, x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_40);
lean_ctor_set(x_90, 0, x_105);
return x_90;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_90, 1);
lean_inc(x_106);
lean_dec(x_90);
x_107 = lean_ctor_get(x_91, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_108 = x_91;
} else {
 lean_dec_ref(x_91);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_22, 1);
lean_inc(x_109);
lean_dec(x_22);
lean_ctor_set(x_40, 1, x_109);
lean_ctor_set(x_40, 0, x_107);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_40);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_40);
lean_dec(x_22);
x_112 = !lean_is_exclusive(x_90);
if (x_112 == 0)
{
return x_90;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_90, 0);
x_114 = lean_ctor_get(x_90, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_90);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_40, 1);
lean_inc(x_116);
lean_dec(x_40);
x_117 = lean_ctor_get(x_24, 1);
lean_inc(x_117);
lean_dec(x_24);
x_118 = l_Lean_Meta_getIntValue_x3f(x_117, x_6, x_7, x_8, x_9, x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_22);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_125 = x_118;
} else {
 lean_dec_ref(x_118);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_119, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_127 = x_119;
} else {
 lean_dec_ref(x_119);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_22, 1);
lean_inc(x_128);
lean_dec(x_22);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_125)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_125;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_124);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_22);
x_132 = lean_ctor_get(x_118, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_118, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_134 = x_118;
} else {
 lean_dec_ref(x_118);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
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
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(1);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_43 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_45;
goto block_37;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = l_Int_Linear_Poly_isZero(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_44);
lean_dec(x_50);
lean_free_object(x_43);
x_52 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_47);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*7 + 10);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_55;
goto block_37;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_52, 1);
x_58 = lean_ctor_get(x_52, 0);
lean_dec(x_58);
x_59 = lean_mk_string_unchecked("monomial expected, found numeral", 32, 32);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
lean_inc(x_1);
x_61 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_52, 7);
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_52, 0, x_60);
x_62 = lean_mk_string_unchecked("\ninternalizing as variable", 26, 26);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_Grind_reportIssue(x_64, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_66;
goto block_37;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_dec(x_52);
x_68 = lean_mk_string_unchecked("monomial expected, found numeral", 32, 32);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
lean_inc(x_1);
x_70 = l_Lean_indentExpr(x_1);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_mk_string_unchecked("\ninternalizing as variable", 26, 26);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Meta_Grind_reportIssue(x_74, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_76;
goto block_37;
}
}
}
else
{
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
lean_ctor_set_tag(x_44, 0);
return x_43;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_44, 0);
lean_inc(x_77);
lean_dec(x_44);
x_78 = l_Int_Linear_Poly_isZero(x_2);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_77);
lean_free_object(x_43);
x_79 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_47);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*7 + 10);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_82;
goto block_37;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_84 = x_79;
} else {
 lean_dec_ref(x_79);
 x_84 = lean_box(0);
}
x_85 = lean_mk_string_unchecked("monomial expected, found numeral", 32, 32);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
lean_inc(x_1);
x_87 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_84)) {
 x_88 = lean_alloc_ctor(7, 2, 0);
} else {
 x_88 = x_84;
 lean_ctor_set_tag(x_88, 7);
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_mk_string_unchecked("\ninternalizing as variable", 26, 26);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Meta_Grind_reportIssue(x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_83);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_93;
goto block_37;
}
}
else
{
lean_object* x_94; 
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
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_77);
lean_ctor_set(x_43, 0, x_94);
return x_43;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_43, 1);
lean_inc(x_95);
lean_dec(x_43);
x_96 = lean_ctor_get(x_44, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_97 = x_44;
} else {
 lean_dec_ref(x_44);
 x_97 = lean_box(0);
}
x_98 = l_Int_Linear_Poly_isZero(x_2);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_97);
lean_dec(x_96);
x_99 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_95);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_100, sizeof(void*)*7 + 10);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_102;
goto block_37;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_104 = x_99;
} else {
 lean_dec_ref(x_99);
 x_104 = lean_box(0);
}
x_105 = lean_mk_string_unchecked("monomial expected, found numeral", 32, 32);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
lean_inc(x_1);
x_107 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_104)) {
 x_108 = lean_alloc_ctor(7, 2, 0);
} else {
 x_108 = x_104;
 lean_ctor_set_tag(x_108, 7);
}
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("\ninternalizing as variable", 26, 26);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Meta_Grind_reportIssue(x_111, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_113;
goto block_37;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
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
if (lean_is_scalar(x_97)) {
 x_114 = lean_alloc_ctor(0, 1, 0);
} else {
 x_114 = x_97;
 lean_ctor_set_tag(x_114, 0);
}
lean_ctor_set(x_114, 0, x_96);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_95);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
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
x_116 = !lean_is_exclusive(x_43);
if (x_116 == 0)
{
return x_43;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_43, 0);
x_118 = lean_ctor_get(x_43, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_43);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_1);
x_120 = lean_ctor_get(x_41, 0);
lean_inc(x_120);
lean_dec(x_41);
x_121 = lean_ctor_get(x_40, 1);
lean_inc(x_121);
lean_dec(x_40);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_grind_cutsat_mk_var(x_123, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_121);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_2);
lean_ctor_set(x_124, 0, x_127);
return x_124;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_124, 0);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_124);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_2);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_122);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_124);
if (x_132 == 0)
{
return x_124;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_124, 0);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_124);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
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
x_136 = !lean_is_exclusive(x_40);
if (x_136 == 0)
{
return x_40;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_40, 0);
x_138 = lean_ctor_get(x_40, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_40);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
block_37:
{
lean_object* x_21; 
x_21 = lean_grind_cutsat_mk_var(x_1, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_to_int(x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_2);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
lean_inc(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_1 = x_20;
x_2 = x_23;
x_11 = x_24;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_1, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_to_int(x_25);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_24, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(x_23, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
return x_30;
}
else
{
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_to_int(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_34, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(x_33, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_41;
}
else
{
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
}
}
}
}
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_IntInstTesters(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
