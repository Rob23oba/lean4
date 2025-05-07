// Lean compiler output
// Module: Lean.Meta.CheckTactic
// Imports: Lean.Meta.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_mk_string_unchecked("Lean", 4, 4);
x_12 = lean_mk_string_unchecked("Meta", 4, 4);
x_13 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_14 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
x_15 = l_Lean_Name_mkStr4(x_11, x_12, x_13, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Expr_const___override(x_15, x_17);
x_19 = l_Lean_mkAppB(x_18, x_2, x_1);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_mk_string_unchecked("Lean", 4, 4);
x_23 = lean_mk_string_unchecked("Meta", 4, 4);
x_24 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_25 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
x_26 = l_Lean_Name_mkStr4(x_22, x_23, x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Expr_const___override(x_26, x_28);
x_30 = l_Lean_mkAppB(x_29, x_2, x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_CheckTactic_mkCheckGoalType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_replaceRef(x_1, x_8);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
x_14 = lean_ctor_get(x_5, 4);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_5, 8);
x_18 = lean_ctor_get(x_5, 9);
x_19 = lean_ctor_get(x_5, 10);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_21 = lean_ctor_get(x_5, 11);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_23 = lean_ctor_get(x_5, 12);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_9);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_17);
lean_ctor_set(x_24, 9, x_18);
lean_ctor_set(x_24, 10, x_19);
lean_ctor_set(x_24, 11, x_21);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*13, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*13 + 1, x_22);
x_25 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_2, x_3, x_4, x_24, x_6, x_7);
lean_dec(x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_Lean_Expr_sort___override(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_unbox(x_14);
lean_inc(x_3);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_13, x_16, x_15, x_3, x_4, x_5, x_6, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_14);
lean_inc(x_3);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_22, x_15, x_3, x_4, x_5, x_6, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Meta", 4, 4);
x_29 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_30 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
x_32 = lean_box(0);
lean_inc(x_10);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_32);
lean_ctor_set(x_23, 0, x_10);
x_33 = l_Lean_Expr_const___override(x_31, x_23);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_mk_empty_array_with_capacity(x_34);
lean_inc(x_19);
x_36 = lean_array_push(x_35, x_19);
lean_inc(x_25);
x_37 = lean_array_push(x_36, x_25);
x_38 = l_Lean_mkAppN(x_33, x_37);
lean_dec(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_38);
lean_inc(x_2);
x_39 = l_Lean_Meta_isExprDefEq(x_2, x_38, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_10);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_mk_string_unchecked("Goal", 4, 4);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_45);
lean_ctor_set(x_17, 0, x_44);
x_46 = lean_mk_string_unchecked("\nis expected to match ", 22, 22);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_47);
lean_ctor_set(x_8, 0, x_17);
x_48 = l_Lean_indentExpr(x_38);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("", 0, 0);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(x_1, x_52, x_3, x_4, x_5, x_6, x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_39);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_39, 0);
lean_dec(x_59);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_25);
lean_ctor_set(x_39, 0, x_8);
return x_39;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_39, 1);
lean_inc(x_60);
lean_dec(x_39);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_25);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_38);
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_39);
if (x_62 == 0)
{
return x_39;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_39, 0);
x_64 = lean_ctor_get(x_39, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_39);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_66 = lean_ctor_get(x_23, 0);
x_67 = lean_ctor_get(x_23, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_23);
x_68 = lean_mk_string_unchecked("Lean", 4, 4);
x_69 = lean_mk_string_unchecked("Meta", 4, 4);
x_70 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_71 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
x_72 = l_Lean_Name_mkStr4(x_68, x_69, x_70, x_71);
x_73 = lean_box(0);
lean_inc(x_10);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_10);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Expr_const___override(x_72, x_74);
x_76 = lean_unsigned_to_nat(2u);
x_77 = lean_mk_empty_array_with_capacity(x_76);
lean_inc(x_19);
x_78 = lean_array_push(x_77, x_19);
lean_inc(x_66);
x_79 = lean_array_push(x_78, x_66);
x_80 = l_Lean_mkAppN(x_75, x_79);
lean_dec(x_79);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_80);
lean_inc(x_2);
x_81 = l_Lean_Meta_isExprDefEq(x_2, x_80, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_10);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_mk_string_unchecked("Goal", 4, 4);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_87);
lean_ctor_set(x_17, 0, x_86);
x_88 = lean_mk_string_unchecked("\nis expected to match ", 22, 22);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_89);
lean_ctor_set(x_8, 0, x_17);
x_90 = l_Lean_indentExpr(x_80);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_8);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("", 0, 0);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(x_1, x_94, x_3, x_4, x_5, x_6, x_84);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_80);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_101 = x_81;
} else {
 lean_dec_ref(x_81);
 x_101 = lean_box(0);
}
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_66);
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_8);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_80);
lean_dec(x_66);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_81, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_107 = lean_ctor_get(x_17, 0);
x_108 = lean_ctor_get(x_17, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_17);
lean_inc(x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_14);
lean_inc(x_3);
x_111 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_109, x_110, x_15, x_3, x_4, x_5, x_6, x_108);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_mk_string_unchecked("Lean", 4, 4);
x_116 = lean_mk_string_unchecked("Meta", 4, 4);
x_117 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_118 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
x_119 = l_Lean_Name_mkStr4(x_115, x_116, x_117, x_118);
x_120 = lean_box(0);
lean_inc(x_10);
if (lean_is_scalar(x_114)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_114;
 lean_ctor_set_tag(x_121, 1);
}
lean_ctor_set(x_121, 0, x_10);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_Expr_const___override(x_119, x_121);
x_123 = lean_unsigned_to_nat(2u);
x_124 = lean_mk_empty_array_with_capacity(x_123);
lean_inc(x_107);
x_125 = lean_array_push(x_124, x_107);
lean_inc(x_112);
x_126 = lean_array_push(x_125, x_112);
x_127 = l_Lean_mkAppN(x_122, x_126);
lean_dec(x_126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_127);
lean_inc(x_2);
x_128 = l_Lean_Meta_isExprDefEq(x_2, x_127, x_3, x_4, x_5, x_6, x_113);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_10);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_mk_string_unchecked("Goal", 4, 4);
x_133 = l_Lean_stringToMessageData(x_132);
lean_dec(x_132);
x_134 = l_Lean_indentExpr(x_2);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_mk_string_unchecked("\nis expected to match ", 22, 22);
x_137 = l_Lean_stringToMessageData(x_136);
lean_dec(x_136);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_137);
lean_ctor_set(x_8, 0, x_135);
x_138 = l_Lean_indentExpr(x_127);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_8);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked("", 0, 0);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(x_1, x_142, x_3, x_4, x_5, x_6, x_131);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_127);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_128, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_149 = x_128;
} else {
 lean_dec_ref(x_128);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_107);
lean_ctor_set(x_150, 1, x_10);
lean_ctor_set(x_8, 1, x_150);
lean_ctor_set(x_8, 0, x_112);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_8);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_127);
lean_dec(x_112);
lean_dec(x_107);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_ctor_get(x_128, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_128, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_154 = x_128;
} else {
 lean_dec_ref(x_128);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_156 = lean_ctor_get(x_8, 0);
x_157 = lean_ctor_get(x_8, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_8);
lean_inc(x_156);
x_158 = l_Lean_Expr_sort___override(x_156);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_box(0);
x_161 = lean_box(0);
x_162 = lean_unbox(x_160);
lean_inc(x_3);
x_163 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_159, x_162, x_161, x_3, x_4, x_5, x_6, x_157);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
lean_inc(x_164);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_164);
x_168 = lean_unbox(x_160);
lean_inc(x_3);
x_169 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_167, x_168, x_161, x_3, x_4, x_5, x_6, x_165);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_mk_string_unchecked("Lean", 4, 4);
x_174 = lean_mk_string_unchecked("Meta", 4, 4);
x_175 = lean_mk_string_unchecked("CheckTactic", 11, 11);
x_176 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
x_177 = l_Lean_Name_mkStr4(x_173, x_174, x_175, x_176);
x_178 = lean_box(0);
lean_inc(x_156);
if (lean_is_scalar(x_172)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_172;
 lean_ctor_set_tag(x_179, 1);
}
lean_ctor_set(x_179, 0, x_156);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_Expr_const___override(x_177, x_179);
x_181 = lean_unsigned_to_nat(2u);
x_182 = lean_mk_empty_array_with_capacity(x_181);
lean_inc(x_164);
x_183 = lean_array_push(x_182, x_164);
lean_inc(x_170);
x_184 = lean_array_push(x_183, x_170);
x_185 = l_Lean_mkAppN(x_180, x_184);
lean_dec(x_184);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_185);
lean_inc(x_2);
x_186 = l_Lean_Meta_isExprDefEq(x_2, x_185, x_3, x_4, x_5, x_6, x_171);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_unbox(x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_170);
lean_dec(x_164);
lean_dec(x_156);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_mk_string_unchecked("Goal", 4, 4);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
x_192 = l_Lean_indentExpr(x_2);
if (lean_is_scalar(x_166)) {
 x_193 = lean_alloc_ctor(7, 2, 0);
} else {
 x_193 = x_166;
 lean_ctor_set_tag(x_193, 7);
}
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_mk_string_unchecked("\nis expected to match ", 22, 22);
x_195 = l_Lean_stringToMessageData(x_194);
lean_dec(x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_indentExpr(x_185);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_mk_string_unchecked("", 0, 0);
x_200 = l_Lean_stringToMessageData(x_199);
lean_dec(x_199);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(x_1, x_201, x_3, x_4, x_5, x_6, x_189);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_185);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = lean_ctor_get(x_186, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_208 = x_186;
} else {
 lean_dec_ref(x_186);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_166;
}
lean_ctor_set(x_209, 0, x_164);
lean_ctor_set(x_209, 1, x_156);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_170);
lean_ctor_set(x_210, 1, x_209);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_207);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_185);
lean_dec(x_170);
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_156);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_212 = lean_ctor_get(x_186, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_186, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_214 = x_186;
} else {
 lean_dec_ref(x_186);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CheckTactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
