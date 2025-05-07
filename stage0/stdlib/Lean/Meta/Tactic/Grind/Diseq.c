// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Diseq
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkDiseqProof_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 4);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_43; uint8_t x_44; 
x_23 = lean_ctor_get(x_17, 1);
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_25 = x_18;
} else {
 lean_dec_ref(x_18);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
x_27 = lean_box(0);
lean_ctor_set(x_17, 1, x_27);
lean_ctor_set(x_17, 0, x_26);
lean_inc(x_14);
x_43 = l_Lean_Expr_cleanupAnnotations(x_14);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_14);
x_3 = x_17;
x_4 = x_16;
x_13 = x_23;
goto _start;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_inc(x_43);
x_46 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_14);
x_3 = x_17;
x_4 = x_16;
x_13 = x_23;
goto _start;
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_inc(x_46);
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_14);
x_3 = x_17;
x_4 = x_16;
x_13 = x_23;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_49);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_53 = lean_mk_string_unchecked("Eq", 2, 2);
x_54 = l_Lean_Name_mkStr1(x_53);
x_55 = l_Lean_Expr_isConstOf(x_52, x_54);
lean_dec(x_54);
lean_dec(x_52);
if (x_55 == 0)
{
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_14);
x_3 = x_17;
x_4 = x_16;
x_13 = x_23;
goto _start;
}
else
{
lean_object* x_57; 
lean_inc(x_14);
x_57 = l_Lean_Meta_Grind_isEqFalse(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_25);
lean_dec(x_14);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_3 = x_17;
x_4 = x_16;
x_13 = x_60;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_43, 1);
lean_inc(x_63);
lean_dec(x_43);
x_64 = lean_ctor_get(x_46, 1);
lean_inc(x_64);
lean_dec(x_46);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_dec(x_49);
x_89 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_64, x_5, x_62);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
x_66 = x_89;
goto block_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_63, x_5, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
x_66 = x_93;
goto block_88;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_65);
lean_inc(x_1);
x_97 = l_Lean_Meta_Grind_hasType(x_1, x_65, x_9, x_10, x_11, x_12, x_96);
x_66 = x_97;
goto block_88;
}
}
block_88:
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_63, x_5, x_69);
lean_dec(x_63);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_65);
lean_dec(x_64);
x_28 = x_70;
goto block_42;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_64, x_5, x_73);
lean_dec(x_64);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_dec(x_65);
x_28 = x_74;
goto block_42;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_78 = l_Lean_Meta_Grind_hasType(x_1, x_65, x_9, x_10, x_11, x_12, x_77);
x_28 = x_78;
goto block_42;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_1);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_dec(x_66);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_14);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_27);
x_83 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_79);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
return x_66;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
x_86 = lean_ctor_get(x_66, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_66);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_17);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_57);
if (x_98 == 0)
{
return x_57;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_57, 0);
x_100 = lean_ctor_get(x_57, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_57);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
}
block_42:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_14);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_3 = x_17;
x_4 = x_16;
x_13 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
if (lean_is_scalar(x_25)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_25;
}
lean_ctor_set(x_34, 0, x_14);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_27);
x_37 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_122; uint8_t x_123; 
x_102 = lean_ctor_get(x_17, 1);
lean_inc(x_102);
lean_dec(x_17);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_103 = x_18;
} else {
 lean_dec_ref(x_18);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_14);
x_122 = l_Lean_Expr_cleanupAnnotations(x_14);
x_123 = l_Lean_Expr_isApp(x_122);
if (x_123 == 0)
{
lean_dec(x_122);
lean_dec(x_103);
lean_dec(x_14);
x_3 = x_106;
x_4 = x_16;
x_13 = x_102;
goto _start;
}
else
{
lean_object* x_125; uint8_t x_126; 
lean_inc(x_122);
x_125 = l_Lean_Expr_appFnCleanup___redArg(x_122);
x_126 = l_Lean_Expr_isApp(x_125);
if (x_126 == 0)
{
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_103);
lean_dec(x_14);
x_3 = x_106;
x_4 = x_16;
x_13 = x_102;
goto _start;
}
else
{
lean_object* x_128; uint8_t x_129; 
lean_inc(x_125);
x_128 = l_Lean_Expr_appFnCleanup___redArg(x_125);
x_129 = l_Lean_Expr_isApp(x_128);
if (x_129 == 0)
{
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_103);
lean_dec(x_14);
x_3 = x_106;
x_4 = x_16;
x_13 = x_102;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_inc(x_128);
x_131 = l_Lean_Expr_appFnCleanup___redArg(x_128);
x_132 = lean_mk_string_unchecked("Eq", 2, 2);
x_133 = l_Lean_Name_mkStr1(x_132);
x_134 = l_Lean_Expr_isConstOf(x_131, x_133);
lean_dec(x_133);
lean_dec(x_131);
if (x_134 == 0)
{
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_103);
lean_dec(x_14);
x_3 = x_106;
x_4 = x_16;
x_13 = x_102;
goto _start;
}
else
{
lean_object* x_136; 
lean_inc(x_14);
x_136 = l_Lean_Meta_Grind_isEqFalse(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_102);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_103);
lean_dec(x_14);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_3 = x_106;
x_4 = x_16;
x_13 = x_139;
goto _start;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_ctor_get(x_122, 1);
lean_inc(x_142);
lean_dec(x_122);
x_143 = lean_ctor_get(x_125, 1);
lean_inc(x_143);
lean_dec(x_125);
x_144 = lean_ctor_get(x_128, 1);
lean_inc(x_144);
lean_dec(x_128);
x_168 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_143, x_5, x_141);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
x_145 = x_168;
goto block_167;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_142, x_5, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
x_145 = x_172;
goto block_167;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_144);
lean_inc(x_1);
x_176 = l_Lean_Meta_Grind_hasType(x_1, x_144, x_9, x_10, x_11, x_12, x_175);
x_145 = x_176;
goto block_167;
}
}
block_167:
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_142, x_5, x_148);
lean_dec(x_142);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_dec(x_144);
lean_dec(x_143);
x_107 = x_149;
goto block_121;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_143, x_5, x_152);
lean_dec(x_143);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_dec(x_144);
x_107 = x_153;
goto block_121;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_157 = l_Lean_Meta_Grind_hasType(x_1, x_144, x_9, x_10, x_11, x_12, x_156);
x_107 = x_157;
goto block_121;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_16);
lean_dec(x_1);
x_158 = lean_ctor_get(x_145, 1);
lean_inc(x_158);
lean_dec(x_145);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_14);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_105);
x_162 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(x_161, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_163 = lean_ctor_get(x_145, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_145, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_165 = x_145;
} else {
 lean_dec_ref(x_145);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_177 = lean_ctor_get(x_136, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_136, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_179 = x_136;
} else {
 lean_dec_ref(x_136);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
}
block_121:
{
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_103);
lean_dec(x_14);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_3 = x_106;
x_4 = x_16;
x_13 = x_110;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_106);
lean_dec(x_16);
lean_dec(x_1);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_dec(x_107);
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_14);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_105);
x_116 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(x_115, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_112);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_119 = x_107;
} else {
 lean_dec_ref(x_107);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_17;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_3);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_13);
return x_182;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0(x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_20 = x_27;
goto block_26;
block_26:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
if (lean_is_scalar(x_19)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_19;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
if (lean_is_scalar(x_19)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_19;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_DTreeMap_Internal_Impl_forInStep___at_____private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_Goal_getRoot(x_13, x_1, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_2);
x_21 = l_Lean_Meta_Grind_Goal_getRoot(x_19, x_2, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_36; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Grind_getParents___redArg(x_16, x_3, x_23);
lean_dec(x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Grind_getParents___redArg(x_22, x_3, x_26);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
x_36 = x_40;
goto block_39;
}
else
{
lean_object* x_41; 
x_41 = lean_unsigned_to_nat(0u);
x_36 = x_41;
goto block_39;
}
block_35:
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_25);
x_33 = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go(x_1, x_2, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_28);
x_34 = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f_go(x_1, x_2, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_2);
return x_34;
}
}
block_39:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
x_30 = x_36;
x_31 = x_37;
goto block_35;
}
else
{
lean_object* x_38; 
x_38 = lean_unsigned_to_nat(0u);
x_30 = x_36;
x_31 = x_38;
goto block_35;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = lean_box(1);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_isDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkDiseqProof_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_14 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_15 = l_instMonadEIO(lean_box(0));
x_16 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, lean_box(0));
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_29);
lean_inc(x_30);
lean_inc(x_27);
lean_inc(x_24);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
x_33 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_35);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_24);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_27);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_30);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_11);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_12);
x_47 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_46);
x_48 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_47);
x_49 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_48);
x_50 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_49);
x_51 = lean_box(0);
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_panic_fn(x_52, x_1);
x_54 = lean_apply_9(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_54;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_53; size_t x_54; uint8_t x_55; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_53 = lean_ptr_addr(x_4);
x_54 = lean_ptr_addr(x_16);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
lean_inc(x_4);
x_56 = lean_grind_mk_eq_proof(x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_mk_string_unchecked("Grind", 5, 5);
x_61 = lean_mk_string_unchecked("ne_of_ne_of_eq_left", 19, 19);
x_62 = l_Lean_Name_mkStr3(x_59, x_60, x_61);
lean_inc(x_2);
x_63 = l_Lean_Expr_const___override(x_62, x_2);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_3);
x_64 = l_Lean_mkApp6(x_63, x_3, x_4, x_16, x_17, x_57, x_18);
x_20 = x_64;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_58;
goto block_52;
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_56;
}
}
else
{
lean_dec(x_16);
x_20 = x_18;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
x_29 = x_14;
goto block_52;
}
block_52:
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = lean_ptr_addr(x_1);
x_31 = lean_ptr_addr(x_17);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_1);
x_33 = lean_grind_mk_eq_proof(x_1, x_17, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_mk_string_unchecked("Lean", 4, 4);
x_37 = lean_mk_string_unchecked("Grind", 5, 5);
x_38 = lean_mk_string_unchecked("ne_of_ne_of_eq_right", 20, 20);
x_39 = l_Lean_Name_mkStr3(x_36, x_37, x_38);
x_40 = l_Lean_Expr_const___override(x_39, x_2);
x_41 = l_Lean_mkApp6(x_40, x_3, x_1, x_4, x_17, x_35, x_20);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Grind", 5, 5);
x_46 = lean_mk_string_unchecked("ne_of_ne_of_eq_right", 20, 20);
x_47 = l_Lean_Name_mkStr3(x_44, x_45, x_46);
x_48 = l_Lean_Expr_const___override(x_47, x_2);
x_49 = l_Lean_mkApp6(x_48, x_3, x_1, x_4, x_17, x_42, x_20);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
}
else
{
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_33;
}
}
else
{
lean_object* x_51; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_19)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_19;
}
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_29);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_42; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_getDiseqFor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
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
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_45);
x_46 = l_Lean_Expr_cleanupAnnotations(x_45);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_44;
goto block_41;
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_inc(x_46);
x_48 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_49 = l_Lean_Expr_isApp(x_48);
if (x_49 == 0)
{
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_44;
goto block_41;
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_inc(x_48);
x_50 = l_Lean_Expr_appFnCleanup___redArg(x_48);
x_51 = l_Lean_Expr_isApp(x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_44;
goto block_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_50);
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_50);
x_53 = lean_mk_string_unchecked("Eq", 2, 2);
x_54 = l_Lean_Name_mkStr1(x_53);
x_55 = l_Lean_Expr_isConstOf(x_52, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_1);
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_44;
goto block_41;
}
else
{
lean_object* x_56; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_56 = l_Lean_Meta_Grind_mkEqFalseProof(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_59 = l_Lean_Meta_mkOfEqFalse(x_57, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
lean_dec(x_46);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_dec(x_48);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
lean_dec(x_50);
x_66 = l_Lean_Expr_constLevels_x21(x_52);
lean_dec(x_52);
x_99 = l_Lean_Meta_Grind_isEqv___redArg(x_1, x_64, x_3, x_61);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
x_67 = x_99;
goto block_98;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_63, x_3, x_102);
x_67 = x_103;
goto block_98;
}
block_98:
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_67, 1);
x_72 = lean_ctor_get(x_67, 0);
lean_dec(x_72);
x_73 = lean_mk_string_unchecked("Ne", 2, 2);
x_74 = lean_mk_string_unchecked("symm", 4, 4);
x_75 = l_Lean_Name_mkStr2(x_73, x_74);
lean_inc(x_66);
x_76 = l_Lean_Expr_const___override(x_75, x_66);
lean_inc(x_63);
lean_inc(x_64);
lean_inc(x_65);
x_77 = l_Lean_mkApp4(x_76, x_65, x_64, x_63, x_60);
lean_ctor_set(x_67, 1, x_77);
lean_ctor_set(x_67, 0, x_64);
if (lean_is_scalar(x_62)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_62;
}
lean_ctor_set(x_78, 0, x_63);
lean_ctor_set(x_78, 1, x_67);
x_79 = l_Lean_Meta_Grind_mkDiseqProof_x3f___lam__0(x_2, x_66, x_65, x_1, x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
x_12 = x_79;
goto block_24;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_67, 1);
lean_inc(x_80);
lean_dec(x_67);
x_81 = lean_mk_string_unchecked("Ne", 2, 2);
x_82 = lean_mk_string_unchecked("symm", 4, 4);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
lean_inc(x_66);
x_84 = l_Lean_Expr_const___override(x_83, x_66);
lean_inc(x_63);
lean_inc(x_64);
lean_inc(x_65);
x_85 = l_Lean_mkApp4(x_84, x_65, x_64, x_63, x_60);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_64);
lean_ctor_set(x_86, 1, x_85);
if (lean_is_scalar(x_62)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_62;
}
lean_ctor_set(x_87, 0, x_63);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Meta_Grind_mkDiseqProof_x3f___lam__0(x_2, x_66, x_65, x_1, x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_80);
x_12 = x_88;
goto block_24;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_67);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_67, 1);
x_91 = lean_ctor_get(x_67, 0);
lean_dec(x_91);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 0, x_63);
if (lean_is_scalar(x_62)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_62;
}
lean_ctor_set(x_92, 0, x_64);
lean_ctor_set(x_92, 1, x_67);
x_93 = l_Lean_Meta_Grind_mkDiseqProof_x3f___lam__0(x_2, x_66, x_65, x_1, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
x_12 = x_93;
goto block_24;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_67, 1);
lean_inc(x_94);
lean_dec(x_67);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_63);
lean_ctor_set(x_95, 1, x_60);
if (lean_is_scalar(x_62)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_62;
}
lean_ctor_set(x_96, 0, x_64);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_Grind_mkDiseqProof_x3f___lam__0(x_2, x_66, x_65, x_1, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_94);
x_12 = x_97;
goto block_24;
}
}
}
}
else
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_46);
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
x_12 = x_59;
goto block_24;
}
}
else
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_46);
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
x_12 = x_56;
goto block_24;
}
}
}
}
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
return x_42;
}
block_24:
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
block_41:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Diseq", 28, 28);
x_35 = lean_mk_string_unchecked("Lean.Meta.Grind.mkDiseqProof\?", 29, 29);
x_36 = lean_unsigned_to_nat(63u);
x_37 = lean_unsigned_to_nat(30u);
x_38 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_Meta_Grind_mkDiseqProof_x3f_spec__0(x_39, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_Grind_mkDiseqProof_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("internal `grind` error, failed to build disequality proof for", 61, 61);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_indentExpr(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("\nand", 4, 4);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_2);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("", 0, 0);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(x_26, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_12, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
