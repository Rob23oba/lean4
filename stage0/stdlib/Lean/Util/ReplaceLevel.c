// Lean compiler output
// Module: Lean.Util.ReplaceLevel
// Imports: Lean.Expr
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
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Level_replace(x_1, x_4);
x_6 = l_Lean_Level_succ___override(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Level_replace(x_1, x_7);
x_10 = l_Lean_Level_replace(x_1, x_8);
x_11 = l_Lean_mkLevelMax_x27(x_9, x_10);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Level_replace(x_1, x_12);
x_15 = l_Lean_Level_replace(x_1, x_13);
x_16 = l_Lean_mkLevelIMax_x27(x_14, x_15);
return x_16;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
return x_17;
}
}
}
static size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize() {
_start:
{
lean_object* x_1; size_t x_2; lean_object* x_3; size_t x_4; size_t x_5; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_usize_of_nat(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_usize_sub(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_uset(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_3);
x_8 = lean_array_uset(x_7, x_1, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceLevelImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Level_replace(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Level_replace(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = lean_usize_mod(x_5, x_2);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
lean_dec(x_7);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = lean_usize_dec_eq(x_9, x_5);
if (x_10 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_11);
x_12 = l_Lean_Level_replace(x_1, x_11);
x_13 = lean_ptr_addr(x_11);
lean_dec(x_11);
x_14 = lean_ptr_addr(x_12);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_sort___override(x_12);
x_17 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_16, x_4);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_12);
lean_inc(x_3);
x_18 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_4);
return x_18;
}
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_box(0);
lean_inc(x_20);
x_22 = l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_20, x_21);
x_23 = l_ptrEqList___redArg(x_20, x_22);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Expr_const___override(x_19, x_22);
x_25 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_24, x_4);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_19);
lean_inc(x_3);
x_26 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_4);
return x_26;
}
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; size_t x_40; size_t x_41; uint8_t x_42; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_1);
x_29 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_27, x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_28);
x_32 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_28, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_40 = lean_ptr_addr(x_27);
lean_dec(x_27);
x_41 = lean_ptr_addr(x_30);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_28);
x_35 = x_42;
goto block_39;
}
else
{
size_t x_43; size_t x_44; uint8_t x_45; 
x_43 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_44 = lean_ptr_addr(x_33);
x_45 = lean_usize_dec_eq(x_43, x_44);
x_35 = x_45;
goto block_39;
}
block_39:
{
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Expr_app___override(x_30, x_33);
x_37 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_36, x_34);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_30);
lean_inc(x_3);
x_38 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_34);
return x_38;
}
}
}
case 6:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_47);
lean_inc(x_1);
x_50 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_47, x_4);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_48);
x_53 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_48, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Expr_lam___override(x_46, x_47, x_48, x_49);
if (lean_obj_tag(x_56) == 6)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; size_t x_69; size_t x_70; uint8_t x_71; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_56, sizeof(void*)*3 + 8);
x_69 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_70 = lean_ptr_addr(x_51);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_dec(x_59);
x_61 = x_71;
goto block_68;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_ptr_addr(x_59);
lean_dec(x_59);
x_73 = lean_ptr_addr(x_54);
x_74 = lean_usize_dec_eq(x_72, x_73);
x_61 = x_74;
goto block_68;
}
block_68:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_56);
x_62 = l_Lean_Expr_lam___override(x_57, x_51, x_54, x_49);
x_63 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_62, x_55);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_60, x_49);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_56);
x_65 = l_Lean_Expr_lam___override(x_57, x_51, x_54, x_49);
x_66 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_65, x_55);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_51);
x_67 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_56, x_55);
return x_67;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_51);
x_75 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_76 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_77 = lean_unsigned_to_nat(1848u);
x_78 = lean_unsigned_to_nat(19u);
x_79 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_80 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_75, x_76, x_77, x_78, x_79);
lean_dec(x_79);
lean_dec(x_76);
lean_dec(x_75);
x_81 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_80);
x_82 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_81, x_55);
return x_82;
}
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 2);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_84);
lean_inc(x_1);
x_87 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_84, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_85);
x_90 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_85, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Expr_forallE___override(x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_93) == 7)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; size_t x_106; size_t x_107; uint8_t x_108; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 2);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_93, sizeof(void*)*3 + 8);
x_106 = lean_ptr_addr(x_95);
lean_dec(x_95);
x_107 = lean_ptr_addr(x_88);
x_108 = lean_usize_dec_eq(x_106, x_107);
if (x_108 == 0)
{
lean_dec(x_96);
x_98 = x_108;
goto block_105;
}
else
{
size_t x_109; size_t x_110; uint8_t x_111; 
x_109 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_110 = lean_ptr_addr(x_91);
x_111 = lean_usize_dec_eq(x_109, x_110);
x_98 = x_111;
goto block_105;
}
block_105:
{
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_93);
x_99 = l_Lean_Expr_forallE___override(x_94, x_88, x_91, x_86);
x_100 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_99, x_92);
return x_100;
}
else
{
uint8_t x_101; 
x_101 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_97, x_86);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
x_102 = l_Lean_Expr_forallE___override(x_94, x_88, x_91, x_86);
x_103 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_102, x_92);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_88);
x_104 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_93, x_92);
return x_104;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_88);
x_112 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_113 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_114 = lean_unsigned_to_nat(1828u);
x_115 = lean_unsigned_to_nat(23u);
x_116 = lean_mk_string_unchecked("forall expected", 15, 15);
x_117 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_112, x_113, x_114, x_115, x_116);
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_112);
x_118 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_117);
x_119 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_118, x_92);
return x_119;
}
}
case 8:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_137; size_t x_143; size_t x_144; uint8_t x_145; 
x_120 = lean_ctor_get(x_3, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_3, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_3, 3);
lean_inc(x_123);
x_124 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_121);
lean_inc(x_1);
x_125 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_121, x_4);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_122);
lean_inc(x_1);
x_128 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_122, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_123);
x_131 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_123, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_143 = lean_ptr_addr(x_121);
lean_dec(x_121);
x_144 = lean_ptr_addr(x_126);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_dec(x_122);
x_137 = x_145;
goto block_142;
}
else
{
size_t x_146; size_t x_147; uint8_t x_148; 
x_146 = lean_ptr_addr(x_122);
lean_dec(x_122);
x_147 = lean_ptr_addr(x_129);
x_148 = lean_usize_dec_eq(x_146, x_147);
x_137 = x_148;
goto block_142;
}
block_136:
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lean_Expr_letE___override(x_120, x_126, x_129, x_132, x_124);
x_135 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_134, x_133);
return x_135;
}
block_142:
{
if (x_137 == 0)
{
lean_dec(x_123);
goto block_136;
}
else
{
size_t x_138; size_t x_139; uint8_t x_140; 
x_138 = lean_ptr_addr(x_123);
lean_dec(x_123);
x_139 = lean_ptr_addr(x_132);
x_140 = lean_usize_dec_eq(x_138, x_139);
if (x_140 == 0)
{
goto block_136;
}
else
{
lean_object* x_141; 
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_120);
lean_inc(x_3);
x_141 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_133);
return x_141;
}
}
}
}
case 10:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; size_t x_154; size_t x_155; uint8_t x_156; 
x_149 = lean_ctor_get(x_3, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_3, 1);
lean_inc(x_150);
lean_inc(x_150);
x_151 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_150, x_4);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ptr_addr(x_150);
lean_dec(x_150);
x_155 = lean_ptr_addr(x_152);
x_156 = lean_usize_dec_eq(x_154, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = l_Lean_Expr_mdata___override(x_149, x_152);
x_158 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_157, x_153);
return x_158;
}
else
{
lean_object* x_159; 
lean_dec(x_152);
lean_dec(x_149);
lean_inc(x_3);
x_159 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_153);
return x_159;
}
}
case 11:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; size_t x_166; size_t x_167; uint8_t x_168; 
x_160 = lean_ctor_get(x_3, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_3, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_3, 2);
lean_inc(x_162);
lean_inc(x_162);
x_163 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_162, x_4);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ptr_addr(x_162);
lean_dec(x_162);
x_167 = lean_ptr_addr(x_164);
x_168 = lean_usize_dec_eq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = l_Lean_Expr_proj___override(x_160, x_161, x_164);
x_170 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_169, x_165);
return x_170;
}
else
{
lean_object* x_171; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_160);
lean_inc(x_3);
x_171 = l_Lean_Expr_ReplaceLevelImpl_cache(x_6, x_3, x_3, x_165);
return x_171;
}
}
default: 
{
lean_object* x_172; 
lean_dec(x_1);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_3);
lean_ctor_set(x_172, 1, x_4);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_3);
lean_dec(x_1);
x_173 = lean_ctor_get(x_4, 1);
lean_inc(x_173);
x_174 = lean_array_uget(x_173, x_6);
lean_dec(x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_4);
return x_175;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache() {
_start:
{
lean_object* x_1; size_t x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_usize_of_nat(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_usize_sub(x_2, x_4);
x_6 = lean_usize_to_nat(x_5);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = lean_mk_array(x_6, x_7);
x_9 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Expr_const___override(x_10, x_11);
x_13 = lean_mk_array(x_6, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_unsigned_to_nat(8192u);
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_usize_of_nat(x_5);
x_7 = lean_usize_sub(x_4, x_6);
x_8 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_9 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_7, x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_3);
x_4 = l_Lean_Level_replace(x_1, x_3);
x_5 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l_Lean_Expr_sort___override(x_4);
return x_8;
}
else
{
lean_dec(x_4);
return x_2;
}
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = l_List_mapTR_loop___at___Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit_spec__0(x_1, x_10, x_11);
x_13 = l_ptrEqList___redArg(x_10, x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Expr_const___override(x_9, x_12);
return x_14;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
return x_2;
}
}
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; size_t x_22; size_t x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_1);
x_17 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_15);
lean_inc(x_16);
x_18 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_16);
x_22 = lean_ptr_addr(x_15);
lean_dec(x_15);
x_23 = lean_ptr_addr(x_17);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_16);
x_19 = x_24;
goto block_21;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_26 = lean_ptr_addr(x_18);
x_27 = lean_usize_dec_eq(x_25, x_26);
x_19 = x_27;
goto block_21;
}
block_21:
{
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = l_Lean_Expr_app___override(x_17, x_18);
return x_20;
}
else
{
lean_dec(x_18);
lean_dec(x_17);
return x_2;
}
}
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_30);
lean_inc(x_29);
x_32 = l_Lean_Expr_lam___override(x_28, x_29, x_30, x_31);
if (lean_obj_tag(x_32) == 6)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; size_t x_44; size_t x_45; uint8_t x_46; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_32, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_37 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_29);
x_38 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_30);
x_44 = lean_ptr_addr(x_34);
lean_dec(x_34);
x_45 = lean_ptr_addr(x_37);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_dec(x_35);
x_39 = x_46;
goto block_43;
}
else
{
size_t x_47; size_t x_48; uint8_t x_49; 
x_47 = lean_ptr_addr(x_35);
lean_dec(x_35);
x_48 = lean_ptr_addr(x_38);
x_49 = lean_usize_dec_eq(x_47, x_48);
x_39 = x_49;
goto block_43;
}
block_43:
{
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_32);
x_40 = l_Lean_Expr_lam___override(x_33, x_37, x_38, x_31);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_36, x_31);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_32);
x_42 = l_Lean_Expr_lam___override(x_33, x_37, x_38, x_31);
return x_42;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
return x_32;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_1);
x_50 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_51 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_52 = lean_unsigned_to_nat(1848u);
x_53 = lean_unsigned_to_nat(19u);
x_54 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_55 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_50, x_51, x_52, x_53, x_54);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_50);
x_56 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_55);
return x_56;
}
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_59);
lean_inc(x_58);
x_61 = l_Lean_Expr_forallE___override(x_57, x_58, x_59, x_60);
if (lean_obj_tag(x_61) == 7)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; size_t x_73; size_t x_74; uint8_t x_75; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 2);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_61, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_66 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_58);
x_67 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_59);
x_73 = lean_ptr_addr(x_63);
lean_dec(x_63);
x_74 = lean_ptr_addr(x_66);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_dec(x_64);
x_68 = x_75;
goto block_72;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_77 = lean_ptr_addr(x_67);
x_78 = lean_usize_dec_eq(x_76, x_77);
x_68 = x_78;
goto block_72;
}
block_72:
{
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_61);
x_69 = l_Lean_Expr_forallE___override(x_62, x_66, x_67, x_60);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_65, x_60);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_61);
x_71 = l_Lean_Expr_forallE___override(x_62, x_66, x_67, x_60);
return x_71;
}
else
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_62);
return x_61;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_1);
x_79 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_80 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_81 = lean_unsigned_to_nat(1828u);
x_82 = lean_unsigned_to_nat(23u);
x_83 = lean_mk_string_unchecked("forall expected", 15, 15);
x_84 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_79, x_80, x_81, x_82, x_83);
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_79);
x_85 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_84);
return x_85;
}
}
case 8:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; size_t x_101; size_t x_102; uint8_t x_103; 
x_86 = lean_ctor_get(x_2, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 3);
lean_inc(x_89);
x_90 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_87);
lean_inc(x_1);
x_91 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_87);
lean_inc(x_88);
lean_inc(x_1);
x_92 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_88);
lean_inc(x_89);
x_93 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_89);
x_101 = lean_ptr_addr(x_87);
lean_dec(x_87);
x_102 = lean_ptr_addr(x_91);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_dec(x_88);
x_94 = x_103;
goto block_100;
}
else
{
size_t x_104; size_t x_105; uint8_t x_106; 
x_104 = lean_ptr_addr(x_88);
lean_dec(x_88);
x_105 = lean_ptr_addr(x_92);
x_106 = lean_usize_dec_eq(x_104, x_105);
x_94 = x_106;
goto block_100;
}
block_100:
{
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_89);
lean_dec(x_2);
x_95 = l_Lean_Expr_letE___override(x_86, x_91, x_92, x_93, x_90);
return x_95;
}
else
{
size_t x_96; size_t x_97; uint8_t x_98; 
x_96 = lean_ptr_addr(x_89);
lean_dec(x_89);
x_97 = lean_ptr_addr(x_93);
x_98 = lean_usize_dec_eq(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_2);
x_99 = l_Lean_Expr_letE___override(x_86, x_91, x_92, x_93, x_90);
return x_99;
}
else
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_86);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; uint8_t x_112; 
x_107 = lean_ctor_get(x_2, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
lean_inc(x_108);
x_109 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_108);
x_110 = lean_ptr_addr(x_108);
lean_dec(x_108);
x_111 = lean_ptr_addr(x_109);
x_112 = lean_usize_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_2);
x_113 = l_Lean_Expr_mdata___override(x_107, x_109);
return x_113;
}
else
{
lean_dec(x_109);
lean_dec(x_107);
return x_2;
}
}
case 11:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; uint8_t x_120; 
x_114 = lean_ctor_get(x_2, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_2, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_2, 2);
lean_inc(x_116);
lean_inc(x_116);
x_117 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_1, x_116);
x_118 = lean_ptr_addr(x_116);
lean_dec(x_116);
x_119 = lean_ptr_addr(x_117);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_2);
x_121 = l_Lean_Expr_proj___override(x_114, x_115, x_117);
return x_121;
}
else
{
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
return x_2;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
