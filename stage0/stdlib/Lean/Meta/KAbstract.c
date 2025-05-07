// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Lean.HeadIndex Lean.Meta.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object*, lean_object*);
uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_256; 
x_256 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_256 == 0)
{
lean_object* x_257; uint8_t x_258; 
lean_inc(x_5);
x_257 = l_Lean_Expr_toHeadIndex(x_5);
x_258 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_257, x_3);
lean_dec(x_257);
if (x_258 == 0)
{
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
goto block_255;
}
else
{
if (x_256 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = l_Lean_Expr_headNumArgs(x_5);
x_260 = lean_nat_dec_eq(x_259, x_4);
lean_dec(x_259);
if (x_260 == 0)
{
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
goto block_255;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_st_ref_get(x_9, x_12);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_5);
x_264 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_unbox(x_265);
lean_dec(x_265);
if (x_266 == 0)
{
lean_object* x_267; 
lean_dec(x_262);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_dec(x_264);
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_267;
goto block_255;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
lean_dec(x_264);
x_269 = lean_st_ref_get(x_7, x_268);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_unsigned_to_nat(1u);
x_273 = lean_nat_add(x_270, x_272);
x_274 = lean_st_ref_set(x_7, x_273, x_271);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_276 = lean_ctor_get(x_274, 1);
x_277 = lean_ctor_get(x_274, 0);
lean_dec(x_277);
x_278 = l_Lean_Meta_Occurrences_contains(x_2, x_270);
lean_dec(x_270);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_free_object(x_274);
x_279 = lean_st_ref_take(x_9, x_276);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_262, 0);
lean_inc(x_282);
lean_dec(x_262);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_280, 2);
lean_inc(x_284);
x_285 = lean_ctor_get(x_280, 3);
lean_inc(x_285);
x_286 = lean_ctor_get(x_280, 4);
lean_inc(x_286);
lean_dec(x_280);
x_287 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_287, 0, x_282);
lean_ctor_set(x_287, 1, x_283);
lean_ctor_set(x_287, 2, x_284);
lean_ctor_set(x_287, 3, x_285);
lean_ctor_set(x_287, 4, x_286);
x_288 = lean_st_ref_set(x_9, x_287, x_281);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_289;
goto block_255;
}
else
{
lean_object* x_290; 
lean_dec(x_262);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_290 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_274, 0, x_290);
return x_274;
}
}
else
{
lean_object* x_291; uint8_t x_292; 
x_291 = lean_ctor_get(x_274, 1);
lean_inc(x_291);
lean_dec(x_274);
x_292 = l_Lean_Meta_Occurrences_contains(x_2, x_270);
lean_dec(x_270);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_st_ref_take(x_9, x_291);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_ctor_get(x_262, 0);
lean_inc(x_296);
lean_dec(x_262);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_294, 2);
lean_inc(x_298);
x_299 = lean_ctor_get(x_294, 3);
lean_inc(x_299);
x_300 = lean_ctor_get(x_294, 4);
lean_inc(x_300);
lean_dec(x_294);
x_301 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_301, 0, x_296);
lean_ctor_set(x_301, 1, x_297);
lean_ctor_set(x_301, 2, x_298);
lean_ctor_set(x_301, 3, x_299);
lean_ctor_set(x_301, 4, x_300);
x_302 = lean_st_ref_set(x_9, x_301, x_295);
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_303;
goto block_255;
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_262);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_304 = l_Lean_Expr_bvar___override(x_6);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_291);
return x_305;
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_262);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_264);
if (x_306 == 0)
{
return x_264;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_264, 0);
x_308 = lean_ctor_get(x_264, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_264);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
else
{
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
goto block_255;
}
}
}
else
{
x_73 = x_7;
x_74 = x_8;
x_75 = x_9;
x_76 = x_10;
x_77 = x_11;
x_78 = x_12;
goto block_255;
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = l_Lean_Expr_app___override(x_13, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
block_35:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_29 = l_Lean_Expr_lam___override(x_22, x_25, x_23, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_26, x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_32 = l_Lean_Expr_lam___override(x_22, x_25, x_23, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_21);
return x_34;
}
}
}
block_50:
{
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
x_44 = l_Lean_Expr_forallE___override(x_42, x_38, x_36, x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_41, x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_37);
x_47 = l_Lean_Expr_forallE___override(x_42, x_38, x_36, x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_36);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
block_59:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Expr_letE___override(x_54, x_51, x_53, x_52, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
block_72:
{
if (x_67 == 0)
{
lean_dec(x_61);
lean_dec(x_5);
x_51 = x_60;
x_52 = x_62;
x_53 = x_63;
x_54 = x_64;
x_55 = x_66;
x_56 = x_65;
goto block_59;
}
else
{
size_t x_68; size_t x_69; uint8_t x_70; 
x_68 = lean_ptr_addr(x_61);
lean_dec(x_61);
x_69 = lean_ptr_addr(x_62);
x_70 = lean_usize_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_dec(x_5);
x_51 = x_60;
x_52 = x_62;
x_53 = x_63;
x_54 = x_64;
x_55 = x_66;
x_56 = x_65;
goto block_59;
}
else
{
lean_object* x_71; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_5);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
}
block_255:
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_5, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_5, 1);
lean_inc(x_80);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_6);
lean_inc(x_79);
lean_inc(x_1);
x_81 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_79, x_6, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_80);
x_84 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_80, x_6, x_73, x_74, x_75, x_76, x_77, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_88 = lean_ptr_addr(x_82);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_dec(x_80);
x_13 = x_82;
x_14 = x_86;
x_15 = x_85;
x_16 = x_89;
goto block_20;
}
else
{
size_t x_90; size_t x_91; uint8_t x_92; 
x_90 = lean_ptr_addr(x_80);
lean_dec(x_80);
x_91 = lean_ptr_addr(x_85);
x_92 = lean_usize_dec_eq(x_90, x_91);
x_13 = x_82;
x_14 = x_86;
x_15 = x_85;
x_16 = x_92;
goto block_20;
}
}
else
{
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_5);
return x_84;
}
}
else
{
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_81;
}
}
case 6:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_5, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_5, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_5, 2);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_6);
lean_inc(x_94);
lean_inc(x_1);
x_97 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_94, x_6, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_6, x_100);
lean_dec(x_6);
lean_inc(x_95);
x_102 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_95, x_101, x_73, x_74, x_75, x_76, x_77, x_99);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
x_106 = l_Lean_Expr_lam___override(x_93, x_94, x_95, x_96);
if (lean_obj_tag(x_106) == 6)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; size_t x_111; size_t x_112; uint8_t x_113; 
lean_free_object(x_102);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 2);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_106, sizeof(void*)*3 + 8);
x_111 = lean_ptr_addr(x_108);
lean_dec(x_108);
x_112 = lean_ptr_addr(x_98);
x_113 = lean_usize_dec_eq(x_111, x_112);
if (x_113 == 0)
{
lean_dec(x_109);
x_21 = x_105;
x_22 = x_107;
x_23 = x_104;
x_24 = x_106;
x_25 = x_98;
x_26 = x_110;
x_27 = x_96;
x_28 = x_113;
goto block_35;
}
else
{
size_t x_114; size_t x_115; uint8_t x_116; 
x_114 = lean_ptr_addr(x_109);
lean_dec(x_109);
x_115 = lean_ptr_addr(x_104);
x_116 = lean_usize_dec_eq(x_114, x_115);
x_21 = x_105;
x_22 = x_107;
x_23 = x_104;
x_24 = x_106;
x_25 = x_98;
x_26 = x_110;
x_27 = x_96;
x_28 = x_116;
goto block_35;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_98);
x_117 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_118 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_119 = lean_unsigned_to_nat(1848u);
x_120 = lean_unsigned_to_nat(19u);
x_121 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_122 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_117, x_118, x_119, x_120, x_121);
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
x_123 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_122);
lean_ctor_set(x_102, 0, x_123);
return x_102;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_102, 0);
x_125 = lean_ctor_get(x_102, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_102);
x_126 = l_Lean_Expr_lam___override(x_93, x_94, x_95, x_96);
if (lean_obj_tag(x_126) == 6)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; size_t x_131; size_t x_132; uint8_t x_133; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 2);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_126, sizeof(void*)*3 + 8);
x_131 = lean_ptr_addr(x_128);
lean_dec(x_128);
x_132 = lean_ptr_addr(x_98);
x_133 = lean_usize_dec_eq(x_131, x_132);
if (x_133 == 0)
{
lean_dec(x_129);
x_21 = x_125;
x_22 = x_127;
x_23 = x_124;
x_24 = x_126;
x_25 = x_98;
x_26 = x_130;
x_27 = x_96;
x_28 = x_133;
goto block_35;
}
else
{
size_t x_134; size_t x_135; uint8_t x_136; 
x_134 = lean_ptr_addr(x_129);
lean_dec(x_129);
x_135 = lean_ptr_addr(x_124);
x_136 = lean_usize_dec_eq(x_134, x_135);
x_21 = x_125;
x_22 = x_127;
x_23 = x_124;
x_24 = x_126;
x_25 = x_98;
x_26 = x_130;
x_27 = x_96;
x_28 = x_136;
goto block_35;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_98);
x_137 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_138 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48, 48);
x_139 = lean_unsigned_to_nat(1848u);
x_140 = lean_unsigned_to_nat(19u);
x_141 = lean_mk_string_unchecked("lambda expected", 15, 15);
x_142 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_137, x_138, x_139, x_140, x_141);
lean_dec(x_141);
lean_dec(x_138);
lean_dec(x_137);
x_143 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_125);
return x_144;
}
}
}
else
{
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
return x_102;
}
}
else
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_1);
return x_97;
}
}
case 7:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_5, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_5, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_5, 2);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_6);
lean_inc(x_146);
lean_inc(x_1);
x_149 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_146, x_6, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_6, x_152);
lean_dec(x_6);
lean_inc(x_147);
x_154 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_147, x_153, x_73, x_74, x_75, x_76, x_77, x_151);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_ctor_get(x_154, 1);
x_158 = l_Lean_Expr_forallE___override(x_145, x_146, x_147, x_148);
if (lean_obj_tag(x_158) == 7)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; size_t x_163; size_t x_164; uint8_t x_165; 
lean_free_object(x_154);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 2);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_158, sizeof(void*)*3 + 8);
x_163 = lean_ptr_addr(x_160);
lean_dec(x_160);
x_164 = lean_ptr_addr(x_150);
x_165 = lean_usize_dec_eq(x_163, x_164);
if (x_165 == 0)
{
lean_dec(x_161);
x_36 = x_156;
x_37 = x_158;
x_38 = x_150;
x_39 = x_148;
x_40 = x_157;
x_41 = x_162;
x_42 = x_159;
x_43 = x_165;
goto block_50;
}
else
{
size_t x_166; size_t x_167; uint8_t x_168; 
x_166 = lean_ptr_addr(x_161);
lean_dec(x_161);
x_167 = lean_ptr_addr(x_156);
x_168 = lean_usize_dec_eq(x_166, x_167);
x_36 = x_156;
x_37 = x_158;
x_38 = x_150;
x_39 = x_148;
x_40 = x_157;
x_41 = x_162;
x_42 = x_159;
x_43 = x_168;
goto block_50;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_150);
x_169 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_170 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_171 = lean_unsigned_to_nat(1828u);
x_172 = lean_unsigned_to_nat(23u);
x_173 = lean_mk_string_unchecked("forall expected", 15, 15);
x_174 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_169, x_170, x_171, x_172, x_173);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_169);
x_175 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_174);
lean_ctor_set(x_154, 0, x_175);
return x_154;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_154, 0);
x_177 = lean_ctor_get(x_154, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_154);
x_178 = l_Lean_Expr_forallE___override(x_145, x_146, x_147, x_148);
if (lean_obj_tag(x_178) == 7)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; size_t x_183; size_t x_184; uint8_t x_185; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 2);
lean_inc(x_181);
x_182 = lean_ctor_get_uint8(x_178, sizeof(void*)*3 + 8);
x_183 = lean_ptr_addr(x_180);
lean_dec(x_180);
x_184 = lean_ptr_addr(x_150);
x_185 = lean_usize_dec_eq(x_183, x_184);
if (x_185 == 0)
{
lean_dec(x_181);
x_36 = x_176;
x_37 = x_178;
x_38 = x_150;
x_39 = x_148;
x_40 = x_177;
x_41 = x_182;
x_42 = x_179;
x_43 = x_185;
goto block_50;
}
else
{
size_t x_186; size_t x_187; uint8_t x_188; 
x_186 = lean_ptr_addr(x_181);
lean_dec(x_181);
x_187 = lean_ptr_addr(x_176);
x_188 = lean_usize_dec_eq(x_186, x_187);
x_36 = x_176;
x_37 = x_178;
x_38 = x_150;
x_39 = x_148;
x_40 = x_177;
x_41 = x_182;
x_42 = x_179;
x_43 = x_188;
goto block_50;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_150);
x_189 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_190 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48, 48);
x_191 = lean_unsigned_to_nat(1828u);
x_192 = lean_unsigned_to_nat(23u);
x_193 = lean_mk_string_unchecked("forall expected", 15, 15);
x_194 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_189, x_190, x_191, x_192, x_193);
lean_dec(x_193);
lean_dec(x_190);
lean_dec(x_189);
x_195 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_177);
return x_196;
}
}
}
else
{
lean_dec(x_150);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
return x_154;
}
}
else
{
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_1);
return x_149;
}
}
case 8:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; 
x_197 = lean_ctor_get(x_5, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_5, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_5, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_5, 3);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_6);
lean_inc(x_198);
lean_inc(x_1);
x_202 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_198, x_6, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_6);
lean_inc(x_199);
lean_inc(x_1);
x_205 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_199, x_6, x_73, x_74, x_75, x_76, x_77, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_add(x_6, x_208);
lean_dec(x_6);
lean_inc(x_200);
x_210 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_200, x_209, x_73, x_74, x_75, x_76, x_77, x_207);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; size_t x_213; size_t x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_ptr_addr(x_198);
lean_dec(x_198);
x_214 = lean_ptr_addr(x_203);
x_215 = lean_usize_dec_eq(x_213, x_214);
if (x_215 == 0)
{
lean_dec(x_199);
x_60 = x_203;
x_61 = x_200;
x_62 = x_211;
x_63 = x_206;
x_64 = x_197;
x_65 = x_201;
x_66 = x_212;
x_67 = x_215;
goto block_72;
}
else
{
size_t x_216; size_t x_217; uint8_t x_218; 
x_216 = lean_ptr_addr(x_199);
lean_dec(x_199);
x_217 = lean_ptr_addr(x_206);
x_218 = lean_usize_dec_eq(x_216, x_217);
x_60 = x_203;
x_61 = x_200;
x_62 = x_211;
x_63 = x_206;
x_64 = x_197;
x_65 = x_201;
x_66 = x_212;
x_67 = x_218;
goto block_72;
}
}
else
{
lean_dec(x_206);
lean_dec(x_203);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_5);
return x_210;
}
}
else
{
lean_dec(x_203);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_205;
}
}
else
{
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_202;
}
}
case 10:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_5, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_5, 1);
lean_inc(x_220);
lean_inc(x_220);
x_221 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_220, x_6, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; size_t x_224; size_t x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_ptr_addr(x_220);
lean_dec(x_220);
x_225 = lean_ptr_addr(x_223);
x_226 = lean_usize_dec_eq(x_224, x_225);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_5);
x_227 = l_Lean_Expr_mdata___override(x_219, x_223);
lean_ctor_set(x_221, 0, x_227);
return x_221;
}
else
{
lean_dec(x_223);
lean_dec(x_219);
lean_ctor_set(x_221, 0, x_5);
return x_221;
}
}
else
{
lean_object* x_228; lean_object* x_229; size_t x_230; size_t x_231; uint8_t x_232; 
x_228 = lean_ctor_get(x_221, 0);
x_229 = lean_ctor_get(x_221, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_221);
x_230 = lean_ptr_addr(x_220);
lean_dec(x_220);
x_231 = lean_ptr_addr(x_228);
x_232 = lean_usize_dec_eq(x_230, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_5);
x_233 = l_Lean_Expr_mdata___override(x_219, x_228);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_229);
return x_234;
}
else
{
lean_object* x_235; 
lean_dec(x_228);
lean_dec(x_219);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_5);
lean_ctor_set(x_235, 1, x_229);
return x_235;
}
}
}
else
{
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_5);
return x_221;
}
}
case 11:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_5, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_5, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_5, 2);
lean_inc(x_238);
lean_inc(x_238);
x_239 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_238, x_6, x_73, x_74, x_75, x_76, x_77, x_78);
if (lean_obj_tag(x_239) == 0)
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; size_t x_242; size_t x_243; uint8_t x_244; 
x_241 = lean_ctor_get(x_239, 0);
x_242 = lean_ptr_addr(x_238);
lean_dec(x_238);
x_243 = lean_ptr_addr(x_241);
x_244 = lean_usize_dec_eq(x_242, x_243);
if (x_244 == 0)
{
lean_object* x_245; 
lean_dec(x_5);
x_245 = l_Lean_Expr_proj___override(x_236, x_237, x_241);
lean_ctor_set(x_239, 0, x_245);
return x_239;
}
else
{
lean_dec(x_241);
lean_dec(x_237);
lean_dec(x_236);
lean_ctor_set(x_239, 0, x_5);
return x_239;
}
}
else
{
lean_object* x_246; lean_object* x_247; size_t x_248; size_t x_249; uint8_t x_250; 
x_246 = lean_ctor_get(x_239, 0);
x_247 = lean_ctor_get(x_239, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_239);
x_248 = lean_ptr_addr(x_238);
lean_dec(x_238);
x_249 = lean_ptr_addr(x_246);
x_250 = lean_usize_dec_eq(x_248, x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_5);
x_251 = l_Lean_Expr_proj___override(x_236, x_237, x_246);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_247);
return x_252;
}
else
{
lean_object* x_253; 
lean_dec(x_246);
lean_dec(x_237);
lean_dec(x_236);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_5);
lean_ctor_set(x_253, 1, x_247);
return x_253;
}
}
}
else
{
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_5);
return x_239;
}
}
default: 
{
lean_object* x_254; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_6);
lean_dec(x_1);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_5);
lean_ctor_set(x_254, 1, x_78);
return x_254;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_35; 
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_35 = l_Lean_Expr_isFVar(x_2);
if (x_35 == 0)
{
x_13 = x_35;
goto block_34;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(0);
lean_inc(x_3);
x_37 = l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(x_3, x_36);
x_13 = x_37;
goto block_34;
}
block_34:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Expr_toHeadIndex(x_2);
x_19 = l_Lean_Expr_headNumArgs(x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_18, x_19, x_10, x_20, x_16, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_16, x_23);
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_dec(x_16);
return x_21;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_2);
x_32 = lean_expr_abstract(x_10, x_31);
lean_dec(x_31);
lean_dec(x_10);
if (lean_is_scalar(x_12)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_12;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_11);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
