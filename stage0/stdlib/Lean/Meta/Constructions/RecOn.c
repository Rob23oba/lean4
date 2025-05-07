// Lean compiler output
// Module: Lean.Meta.Constructions.RecOn
// Imports: Lean.Meta.InferType Lean.AuxRecursor Lean.AddDecl Lean.Meta.CompletionName
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
LEAN_EXPORT lean_object* l_mkRecOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___mkRecOn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___mkRecOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecOnName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___mkRecOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkRecOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_mkRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___mkRecOn_spec__0(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Level_param___override(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Level_param___override(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_19; lean_object* x_25; uint8_t x_26; 
x_8 = lean_st_ref_get(x_6, x_7);
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
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
lean_dec(x_9);
lean_inc(x_25);
x_26 = l_Lean_Environment_hasUnsafe(x_25, x_3);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Environment_hasUnsafe(x_25, x_4);
x_19 = x_27;
goto block_24;
}
else
{
lean_dec(x_25);
x_19 = x_26;
goto block_24;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_12);
if (lean_is_scalar(x_11)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_11;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
block_24:
{
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_12 = x_21;
goto block_18;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_12 = x_23;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_11);
x_14 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_10, x_1, x_2, x_13, x_12);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 3);
lean_inc(x_17);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_6, 0, x_19);
x_20 = lean_ctor_get(x_8, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_6);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_st_ref_set(x_4, x_23, x_9);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_inc(x_18);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_18);
lean_inc(x_18);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_18);
lean_inc(x_18);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_18);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_18);
lean_inc(x_33);
lean_inc(x_30);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_33);
x_35 = lean_ctor_get(x_27, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 4);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_st_ref_set(x_3, x_38, x_28);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_box(0);
x_50 = lean_box(0);
x_51 = lean_unbox(x_49);
x_52 = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(x_48, x_1, x_2, x_51, x_50);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 3);
lean_inc(x_55);
x_56 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_inc(x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_46, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 7);
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_54);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_58);
lean_ctor_set(x_62, 5, x_59);
lean_ctor_set(x_62, 6, x_60);
lean_ctor_set(x_62, 7, x_61);
x_63 = lean_st_ref_set(x_4, x_62, x_47);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_take(x_3, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_inc(x_56);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_56);
lean_inc(x_56);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_56);
lean_inc(x_56);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_56);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_56);
lean_inc(x_72);
lean_inc(x_69);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_69);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_72);
x_74 = lean_ctor_get(x_66, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_66, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_66, 4);
lean_inc(x_76);
lean_dec(x_66);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set(x_77, 4, x_76);
x_78 = lean_st_ref_set(x_3, x_77, x_67);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___redArg(x_1, x_2, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___mkRecOn_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___redArg(x_1, x_8, x_3, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_mkRecOn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_11 = lean_box(0);
x_12 = lean_array_get_size(x_4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_nat_sub(x_14, x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
lean_inc(x_4);
x_20 = l_Array_toSubarray___redArg(x_4, x_19, x_18);
x_21 = lean_nat_add(x_18, x_13);
x_22 = lean_nat_add(x_21, x_17);
x_23 = lean_nat_add(x_22, x_15);
lean_dec(x_22);
lean_inc(x_21);
lean_inc(x_4);
x_24 = l_Array_toSubarray___redArg(x_4, x_21, x_23);
x_25 = l_Array_ofSubarray___redArg(x_20);
lean_dec(x_20);
x_26 = l_Array_ofSubarray___redArg(x_24);
lean_dec(x_24);
x_27 = l_Array_append(lean_box(0), x_25, x_26);
lean_dec(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Array_toSubarray___redArg(x_27, x_19, x_28);
lean_inc(x_4);
x_30 = l_Array_toSubarray___redArg(x_4, x_18, x_21);
x_31 = l_Array_ofSubarray___redArg(x_29);
lean_dec(x_29);
x_32 = l_Array_ofSubarray___redArg(x_30);
lean_dec(x_30);
x_33 = l_Array_append(lean_box(0), x_31, x_32);
lean_dec(x_32);
x_34 = lean_array_get_size(x_33);
x_35 = l_Array_toSubarray___redArg(x_33, x_19, x_34);
x_36 = l_Array_ofSubarray___redArg(x_35);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = lean_box(1);
x_39 = lean_box(1);
x_40 = lean_unbox(x_37);
x_41 = lean_unbox(x_38);
x_42 = lean_unbox(x_39);
x_43 = l_Lean_Meta_mkForallFVars(x_36, x_5, x_40, x_41, x_42, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_dec(x_2);
lean_inc(x_47);
x_48 = l_List_mapTR_loop___at___mkRecOn_spec__0(x_47, x_11);
x_49 = l_Lean_Expr_const___override(x_46, x_48);
x_50 = l_Lean_mkAppN(x_49, x_4);
lean_dec(x_4);
x_51 = lean_unbox(x_37);
x_52 = lean_unbox(x_38);
x_53 = lean_unbox(x_37);
x_54 = lean_unbox(x_39);
x_55 = l_Lean_Meta_mkLambdaFVars(x_36, x_50, x_51, x_52, x_53, x_54, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_36);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_mkRecOnName(x_3);
x_59 = lean_box(1);
x_60 = l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___redArg(x_58, x_47, x_44, x_56, x_59, x_9, x_57);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_55);
if (x_61 == 0)
{
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_55, 0);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_55);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_43);
if (x_65 == 0)
{
return x_43;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_43, 0);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_43);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_mkRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = l_Lean_mkRecName(x_1);
lean_inc(x_7);
x_8 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_mkRecOn___lam__0___boxed), 10, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_15, x_14, x_17, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_19);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_addDecl(x_9, x_4, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_24);
x_25 = l_Lean_setReducibleAttribute___at___mkRecOn_spec__2(x_24, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_5, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_inc(x_24);
x_32 = l_Lean_markAuxRecursor(x_31, x_24);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 3);
lean_inc(x_35);
x_36 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_37);
lean_ctor_set(x_27, 1, x_37);
lean_ctor_set(x_27, 0, x_37);
x_38 = lean_ctor_get(x_29, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_29, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_29, 7);
lean_inc(x_40);
lean_dec(x_29);
lean_inc(x_27);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_34);
lean_ctor_set(x_41, 3, x_35);
lean_ctor_set(x_41, 4, x_27);
lean_ctor_set(x_41, 5, x_38);
lean_ctor_set(x_41, 6, x_39);
lean_ctor_set(x_41, 7, x_40);
x_42 = lean_st_ref_set(x_5, x_41, x_30);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_st_ref_take(x_3, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_inc(x_36);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_36);
lean_inc(x_36);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_36);
lean_inc(x_36);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_36);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_36);
lean_inc(x_51);
lean_inc(x_48);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_48);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_51);
x_53 = lean_ctor_get(x_45, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_45, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 4);
lean_inc(x_55);
lean_dec(x_45);
lean_inc(x_52);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_54);
lean_ctor_set(x_56, 4, x_55);
x_57 = lean_st_ref_set(x_3, x_56, x_46);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_take(x_5, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = l_Lean_addProtected(x_62, x_24);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_60, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_60, 7);
lean_inc(x_69);
lean_dec(x_60);
x_70 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_66);
lean_ctor_set(x_70, 4, x_27);
lean_ctor_set(x_70, 5, x_67);
lean_ctor_set(x_70, 6, x_68);
lean_ctor_set(x_70, 7, x_69);
x_71 = lean_st_ref_set(x_5, x_70, x_61);
lean_dec(x_5);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_take(x_3, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 4);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_52);
lean_ctor_set(x_80, 2, x_77);
lean_ctor_set(x_80, 3, x_78);
lean_ctor_set(x_80, 4, x_79);
x_81 = lean_st_ref_set(x_3, x_80, x_75);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_88 = lean_ctor_get(x_27, 0);
x_89 = lean_ctor_get(x_27, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_27);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_inc(x_24);
x_91 = l_Lean_markAuxRecursor(x_90, x_24);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 3);
lean_inc(x_94);
x_95 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_95);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_inc(x_96);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_ctor_get(x_88, 5);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 7);
lean_inc(x_100);
lean_dec(x_88);
lean_inc(x_97);
x_101 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_92);
lean_ctor_set(x_101, 2, x_93);
lean_ctor_set(x_101, 3, x_94);
lean_ctor_set(x_101, 4, x_97);
lean_ctor_set(x_101, 5, x_98);
lean_ctor_set(x_101, 6, x_99);
lean_ctor_set(x_101, 7, x_100);
x_102 = lean_st_ref_set(x_5, x_101, x_89);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_st_ref_take(x_3, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_inc(x_95);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_95);
lean_inc(x_95);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_95);
lean_inc(x_95);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_95);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_95);
lean_inc(x_111);
lean_inc(x_108);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_110);
lean_ctor_set(x_112, 3, x_108);
lean_ctor_set(x_112, 4, x_111);
lean_ctor_set(x_112, 5, x_111);
x_113 = lean_ctor_get(x_105, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_105, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_105, 4);
lean_inc(x_115);
lean_dec(x_105);
lean_inc(x_112);
x_116 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 3, x_114);
lean_ctor_set(x_116, 4, x_115);
x_117 = lean_st_ref_set(x_3, x_116, x_106);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_st_ref_take(x_5, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = l_Lean_addProtected(x_122, x_24);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 5);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 6);
lean_inc(x_128);
x_129 = lean_ctor_get(x_120, 7);
lean_inc(x_129);
lean_dec(x_120);
x_130 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_130, 0, x_123);
lean_ctor_set(x_130, 1, x_124);
lean_ctor_set(x_130, 2, x_125);
lean_ctor_set(x_130, 3, x_126);
lean_ctor_set(x_130, 4, x_97);
lean_ctor_set(x_130, 5, x_127);
lean_ctor_set(x_130, 6, x_128);
lean_ctor_set(x_130, 7, x_129);
x_131 = lean_st_ref_set(x_5, x_130, x_121);
lean_dec(x_5);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_3, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 4);
lean_inc(x_139);
lean_dec(x_134);
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_112);
lean_ctor_set(x_140, 2, x_137);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_139);
x_141 = lean_st_ref_set(x_3, x_140, x_135);
lean_dec(x_3);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
}
else
{
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
else
{
uint8_t x_146; 
lean_free_object(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = !lean_is_exclusive(x_18);
if (x_146 == 0)
{
return x_18;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_18, 0);
x_148 = lean_ctor_get(x_18, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_18);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_9, 0);
lean_inc(x_150);
lean_dec(x_9);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_inc(x_151);
x_152 = lean_alloc_closure((void*)(l_mkRecOn___lam__0___boxed), 10, 3);
lean_closure_set(x_152, 0, x_150);
lean_closure_set(x_152, 1, x_151);
lean_closure_set(x_152, 2, x_1);
x_153 = lean_ctor_get(x_151, 2);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_box(0);
x_155 = lean_unbox(x_154);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_156 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_153, x_152, x_155, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_157);
lean_inc(x_5);
lean_inc(x_4);
x_160 = l_Lean_addDecl(x_159, x_4, x_5, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
lean_dec(x_157);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_163);
x_164 = l_Lean_setReducibleAttribute___at___mkRecOn_spec__2(x_163, x_2, x_3, x_4, x_5, x_161);
lean_dec(x_4);
lean_dec(x_2);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_st_ref_take(x_5, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
lean_inc(x_163);
x_171 = l_Lean_markAuxRecursor(x_170, x_163);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_167, 3);
lean_inc(x_174);
x_175 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_175);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
lean_inc(x_176);
if (lean_is_scalar(x_169)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_169;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_ctor_get(x_167, 5);
lean_inc(x_178);
x_179 = lean_ctor_get(x_167, 6);
lean_inc(x_179);
x_180 = lean_ctor_get(x_167, 7);
lean_inc(x_180);
lean_dec(x_167);
lean_inc(x_177);
x_181 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_181, 0, x_171);
lean_ctor_set(x_181, 1, x_172);
lean_ctor_set(x_181, 2, x_173);
lean_ctor_set(x_181, 3, x_174);
lean_ctor_set(x_181, 4, x_177);
lean_ctor_set(x_181, 5, x_178);
lean_ctor_set(x_181, 6, x_179);
lean_ctor_set(x_181, 7, x_180);
x_182 = lean_st_ref_set(x_5, x_181, x_168);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_st_ref_take(x_3, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
lean_inc(x_175);
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_175);
lean_inc(x_175);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_175);
lean_inc(x_175);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_175);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_175);
lean_inc(x_191);
lean_inc(x_188);
x_192 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_189);
lean_ctor_set(x_192, 2, x_190);
lean_ctor_set(x_192, 3, x_188);
lean_ctor_set(x_192, 4, x_191);
lean_ctor_set(x_192, 5, x_191);
x_193 = lean_ctor_get(x_185, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_185, 4);
lean_inc(x_195);
lean_dec(x_185);
lean_inc(x_192);
x_196 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_196, 0, x_187);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set(x_196, 4, x_195);
x_197 = lean_st_ref_set(x_3, x_196, x_186);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_st_ref_take(x_5, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = l_Lean_addProtected(x_202, x_163);
x_204 = lean_ctor_get(x_200, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 6);
lean_inc(x_208);
x_209 = lean_ctor_get(x_200, 7);
lean_inc(x_209);
lean_dec(x_200);
x_210 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_206);
lean_ctor_set(x_210, 4, x_177);
lean_ctor_set(x_210, 5, x_207);
lean_ctor_set(x_210, 6, x_208);
lean_ctor_set(x_210, 7, x_209);
x_211 = lean_st_ref_set(x_5, x_210, x_201);
lean_dec(x_5);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_st_ref_take(x_3, x_212);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 2);
lean_inc(x_217);
x_218 = lean_ctor_get(x_214, 3);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 4);
lean_inc(x_219);
lean_dec(x_214);
x_220 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_192);
lean_ctor_set(x_220, 2, x_217);
lean_ctor_set(x_220, 3, x_218);
lean_ctor_set(x_220, 4, x_219);
x_221 = lean_st_ref_set(x_3, x_220, x_215);
lean_dec(x_3);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
x_224 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
else
{
lean_dec(x_157);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_160;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_226 = lean_ctor_get(x_156, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_156, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_228 = x_156;
} else {
 lean_dec_ref(x_156);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_9);
lean_dec(x_1);
x_230 = lean_ctor_get(x_8, 1);
lean_inc(x_230);
lean_dec(x_8);
x_231 = lean_mk_string_unchecked("", 0, 0);
x_232 = l_Lean_stringToMessageData(x_231);
lean_dec(x_231);
x_233 = l_Lean_MessageData_ofName(x_7);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_mk_string_unchecked(" not a recinfo", 14, 14);
x_236 = l_Lean_stringToMessageData(x_235);
lean_dec(x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_237, x_2, x_3, x_4, x_5, x_230);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_238;
}
}
else
{
uint8_t x_239; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_8);
if (x_239 == 0)
{
return x_8;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_8, 0);
x_241 = lean_ctor_get(x_8, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_8);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkDefinitionValInferrringUnsafe___at___mkRecOn_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___redArg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_setReducibilityStatus___at___Lean_setReducibleAttribute___at___mkRecOn_spec__2_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___mkRecOn_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setReducibleAttribute___at___mkRecOn_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_mkRecOn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_mkRecOn___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_11;
}
}
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_RecOn(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
