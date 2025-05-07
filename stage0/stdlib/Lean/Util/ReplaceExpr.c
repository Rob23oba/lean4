// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: Lean.Expr Lean.Util.PtrSet
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
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceImpl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_replace_expr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_replace_expr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_replace(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_11; size_t x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Expr_replaceNoCache(x_1, x_4);
lean_inc(x_5);
x_7 = l_Lean_Expr_replaceNoCache(x_1, x_5);
x_11 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_12 = lean_ptr_addr(x_6);
x_13 = lean_usize_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_5);
x_8 = x_13;
goto block_10;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_15 = lean_ptr_addr(x_7);
x_16 = lean_usize_dec_eq(x_14, x_15);
x_8 = x_16;
goto block_10;
}
block_10:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_Expr_app___override(x_6, x_7);
return x_9;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
}
}
case 6:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_19);
lean_inc(x_18);
x_21 = l_Lean_Expr_lam___override(x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 6)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; size_t x_33; size_t x_34; uint8_t x_35; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_21, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_26 = l_Lean_Expr_replaceNoCache(x_1, x_18);
x_27 = l_Lean_Expr_replaceNoCache(x_1, x_19);
x_33 = lean_ptr_addr(x_23);
lean_dec(x_23);
x_34 = lean_ptr_addr(x_26);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_dec(x_24);
x_28 = x_35;
goto block_32;
}
else
{
size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = lean_ptr_addr(x_24);
lean_dec(x_24);
x_37 = lean_ptr_addr(x_27);
x_38 = lean_usize_dec_eq(x_36, x_37);
x_28 = x_38;
goto block_32;
}
block_32:
{
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_21);
x_29 = l_Lean_Expr_lam___override(x_22, x_26, x_27, x_20);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_25, x_20);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_21);
x_31 = l_Lean_Expr_lam___override(x_22, x_26, x_27, x_20);
return x_31;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
return x_21;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_39 = l_Lean_instInhabitedExpr;
x_40 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_41 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_42 = lean_unsigned_to_nat(1848u);
x_43 = lean_unsigned_to_nat(19u);
x_44 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_45 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_40, x_41, x_42, x_43, x_44);
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_40);
x_46 = l_panic___redArg(x_39, x_45);
return x_46;
}
}
case 7:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_49);
lean_inc(x_48);
x_51 = l_Lean_Expr_forallE___override(x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_51) == 7)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; size_t x_63; size_t x_64; uint8_t x_65; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 2);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_51, sizeof(void*)*3 + 8);
lean_inc(x_1);
x_56 = l_Lean_Expr_replaceNoCache(x_1, x_48);
x_57 = l_Lean_Expr_replaceNoCache(x_1, x_49);
x_63 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_64 = lean_ptr_addr(x_56);
x_65 = lean_usize_dec_eq(x_63, x_64);
if (x_65 == 0)
{
lean_dec(x_54);
x_58 = x_65;
goto block_62;
}
else
{
size_t x_66; size_t x_67; uint8_t x_68; 
x_66 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_67 = lean_ptr_addr(x_57);
x_68 = lean_usize_dec_eq(x_66, x_67);
x_58 = x_68;
goto block_62;
}
block_62:
{
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_51);
x_59 = l_Lean_Expr_forallE___override(x_52, x_56, x_57, x_50);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_55, x_50);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_51);
x_61 = l_Lean_Expr_forallE___override(x_52, x_56, x_57, x_50);
return x_61;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_52);
return x_51;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_1);
x_69 = l_Lean_instInhabitedExpr;
x_70 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_71 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_72 = lean_unsigned_to_nat(1828u);
x_73 = lean_unsigned_to_nat(23u);
x_74 = lean_mk_string_unchecked("forall expected", 15, 15);
x_75 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_70, x_71, x_72, x_73, x_74);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_70);
x_76 = l_panic___redArg(x_69, x_75);
return x_76;
}
}
case 8:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; size_t x_92; size_t x_93; uint8_t x_94; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 3);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_78);
lean_inc(x_1);
x_82 = l_Lean_Expr_replaceNoCache(x_1, x_78);
lean_inc(x_79);
lean_inc(x_1);
x_83 = l_Lean_Expr_replaceNoCache(x_1, x_79);
lean_inc(x_80);
x_84 = l_Lean_Expr_replaceNoCache(x_1, x_80);
x_92 = lean_ptr_addr(x_78);
lean_dec(x_78);
x_93 = lean_ptr_addr(x_82);
x_94 = lean_usize_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_dec(x_79);
x_85 = x_94;
goto block_91;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_96 = lean_ptr_addr(x_83);
x_97 = lean_usize_dec_eq(x_95, x_96);
x_85 = x_97;
goto block_91;
}
block_91:
{
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_2);
x_86 = l_Lean_Expr_letE___override(x_77, x_82, x_83, x_84, x_81);
return x_86;
}
else
{
size_t x_87; size_t x_88; uint8_t x_89; 
x_87 = lean_ptr_addr(x_80);
lean_dec(x_80);
x_88 = lean_ptr_addr(x_84);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_2);
x_90 = l_Lean_Expr_letE___override(x_77, x_82, x_83, x_84, x_81);
return x_90;
}
else
{
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_77);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_2, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
lean_inc(x_99);
x_100 = l_Lean_Expr_replaceNoCache(x_1, x_99);
x_101 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_102 = lean_ptr_addr(x_100);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_2);
x_104 = l_Lean_Expr_mdata___override(x_98, x_100);
return x_104;
}
else
{
lean_dec(x_100);
lean_dec(x_98);
return x_2;
}
}
case 11:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; size_t x_110; uint8_t x_111; 
x_105 = lean_ctor_get(x_2, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_2, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
lean_inc(x_107);
x_108 = l_Lean_Expr_replaceNoCache(x_1, x_107);
x_109 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_110 = lean_ptr_addr(x_108);
x_111 = lean_usize_dec_eq(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_2);
x_112 = l_Lean_Expr_proj___override(x_105, x_106, x_108);
return x_112;
}
else
{
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_105);
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
else
{
lean_object* x_113; 
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_3, 0);
lean_inc(x_113);
lean_dec(x_3);
return x_113;
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
