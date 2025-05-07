// Lean compiler output
// Module: Lean.Server.Completion.CompletionResolution
// Imports: Lean.Server.Completion.CompletionItemData Lean.Server.Completion.CompletionInfoSelection
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3059_(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_24____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Window_0__toJsonShowMessageParams____x40_Lean_Data_Lsp_Window___hyg_245__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(lean_object*);
lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedDeprecationEntry;
lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_24____boxed(lean_object*);
lean_object* l_Lean_Elab_CompletionInfo_lctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonResolvableCompletionItemData;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionIdentifier;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Position_0__Lean_fromJsonPosition____x40_Lean_Data_Position___hyg_289__spec__0(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonResolvableCompletionItemData;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_158_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionIdentifier;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262_(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_mk_string_unchecked("const", 5, 5);
x_16 = lean_mk_string_unchecked("declName", 8, 8);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_mk_empty_array_with_capacity(x_1);
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Json_parseTagged(x_2, x_15, x_1, x_20);
lean_dec(x_20);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Except_orElseLazy___redArg(x_21, x_3);
lean_dec(x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Except_orElseLazy___redArg(x_25, x_3);
lean_dec(x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get(x_4, x_27, x_28);
lean_dec(x_27);
lean_inc(x_29);
x_30 = l_Lean_Json_getStr_x3f(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_6 = x_31;
goto block_9;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_34 = lean_string_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_String_toName(x_32);
x_36 = l_Lean_Name_isAnonymous(x_35);
if (x_36 == 0)
{
lean_dec(x_29);
x_10 = x_35;
goto block_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_37 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_38 = lean_unsigned_to_nat(80u);
x_39 = l_Lean_Json_pretty(x_29, x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = lean_mk_string_unchecked("'", 1, 1);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_6 = x_42;
goto block_9;
}
}
else
{
lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_29);
x_43 = lean_box(0);
x_10 = x_43;
goto block_14;
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Except_orElseLazy___redArg(x_7, x_3);
lean_dec(x_7);
return x_8;
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Except_orElseLazy___redArg(x_12, x_3);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_24____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("fvar", 4, 4);
x_5 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_24____boxed), 5, 4);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_16 = lean_mk_string_unchecked("id", 2, 2);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_mk_empty_array_with_capacity(x_5);
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_20);
lean_dec(x_20);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Except_orElseLazy___redArg(x_21, x_6);
lean_dec(x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Except_orElseLazy___redArg(x_25, x_6);
lean_dec(x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get(x_3, x_27, x_28);
lean_dec(x_27);
lean_inc(x_29);
x_30 = l_Lean_Json_getStr_x3f(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_12 = x_31;
goto block_15;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("[anonymous]", 11, 11);
x_34 = lean_string_dec_eq(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_String_toName(x_32);
x_36 = l_Lean_Name_isAnonymous(x_35);
if (x_36 == 0)
{
lean_dec(x_29);
x_7 = x_35;
goto block_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_35);
x_37 = lean_mk_string_unchecked("expected a `Name`, got '", 24, 24);
x_38 = lean_unsigned_to_nat(80u);
x_39 = l_Lean_Json_pretty(x_29, x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = lean_mk_string_unchecked("'", 1, 1);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_12 = x_42;
goto block_15;
}
}
else
{
lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_29);
x_43 = lean_box(0);
x_7 = x_43;
goto block_11;
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Except_orElseLazy___redArg(x_9, x_6);
lean_dec(x_9);
return x_10;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Except_orElseLazy___redArg(x_13, x_6);
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_24____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_24_), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_158_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_5 = lean_mk_string_unchecked("const", 5, 5);
x_6 = lean_mk_string_unchecked("declName", 8, 8);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Name_toString(x_3, x_8, x_4);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = l_Lean_Json_mkObj(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_19 = lean_mk_string_unchecked("const", 5, 5);
x_20 = lean_mk_string_unchecked("declName", 8, 8);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Name_toString(x_17, x_22, x_18);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Json_mkObj(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = l_Lean_Json_mkObj(x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_35 = lean_mk_string_unchecked("fvar", 4, 4);
x_36 = lean_mk_string_unchecked("id", 2, 2);
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Name_toString(x_33, x_38, x_34);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Json_mkObj(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
x_46 = l_Lean_Json_mkObj(x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_49 = lean_mk_string_unchecked("fvar", 4, 4);
x_50 = lean_mk_string_unchecked("id", 2, 2);
x_51 = lean_box(1);
x_52 = lean_unbox(x_51);
x_53 = l_Lean_Name_toString(x_47, x_52, x_48);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Json_mkObj(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
x_61 = l_Lean_Json_mkObj(x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158_(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonCompletionIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_158_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_24_(x_3);
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
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("params", 6, 6);
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionItemData_0__Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_15__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Lsp", 3, 3);
x_9 = lean_mk_string_unchecked("ResolvableCompletionItemData", 28, 28);
x_10 = l_Lean_Name_mkStr3(x_7, x_8, x_9);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_6);
x_13 = l_Lean_Name_toString(x_10, x_12, x_6);
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_Name_mkStr1(x_2);
x_17 = lean_unbox(x_11);
x_18 = l_Lean_Name_toString(x_16, x_17, x_6);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_25 = lean_mk_string_unchecked("Lean", 4, 4);
x_26 = lean_mk_string_unchecked("Lsp", 3, 3);
x_27 = lean_mk_string_unchecked("ResolvableCompletionItemData", 28, 28);
x_28 = l_Lean_Name_mkStr3(x_25, x_26, x_27);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
lean_inc(x_24);
x_31 = l_Lean_Name_toString(x_28, x_30, x_24);
x_32 = lean_mk_string_unchecked(".", 1, 1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_Name_mkStr1(x_2);
x_35 = lean_unbox(x_29);
x_36 = l_Lean_Name_toString(x_34, x_35, x_24);
x_37 = lean_string_append(x_33, x_36);
lean_dec(x_36);
x_38 = lean_mk_string_unchecked(": ", 2, 2);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_23);
lean_dec(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_3, 0);
lean_inc(x_45);
lean_dec(x_3);
x_46 = lean_mk_string_unchecked("cPos", 4, 4);
lean_inc(x_1);
x_47 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_Position_0__Lean_fromJsonPosition____x40_Lean_Data_Position___hyg_289__spec__0(x_1, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_51 = lean_mk_string_unchecked("Lean", 4, 4);
x_52 = lean_mk_string_unchecked("Lsp", 3, 3);
x_53 = lean_mk_string_unchecked("ResolvableCompletionItemData", 28, 28);
x_54 = l_Lean_Name_mkStr3(x_51, x_52, x_53);
x_55 = lean_box(1);
x_56 = lean_unbox(x_55);
lean_inc(x_50);
x_57 = l_Lean_Name_toString(x_54, x_56, x_50);
x_58 = lean_mk_string_unchecked(".", 1, 1);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = l_Lean_Name_mkStr1(x_46);
x_61 = lean_unbox(x_55);
x_62 = l_Lean_Name_toString(x_60, x_61, x_50);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
x_64 = lean_mk_string_unchecked(": ", 2, 2);
x_65 = lean_string_append(x_63, x_64);
lean_dec(x_64);
x_66 = lean_string_append(x_65, x_49);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_66);
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
lean_dec(x_47);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Lsp", 3, 3);
x_71 = lean_mk_string_unchecked("ResolvableCompletionItemData", 28, 28);
x_72 = l_Lean_Name_mkStr3(x_69, x_70, x_71);
x_73 = lean_box(1);
x_74 = lean_unbox(x_73);
lean_inc(x_68);
x_75 = l_Lean_Name_toString(x_72, x_74, x_68);
x_76 = lean_mk_string_unchecked(".", 1, 1);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = l_Lean_Name_mkStr1(x_46);
x_79 = lean_unbox(x_73);
x_80 = l_Lean_Name_toString(x_78, x_79, x_68);
x_81 = lean_string_append(x_77, x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked(": ", 2, 2);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_string_append(x_83, x_67);
lean_dec(x_67);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_86; 
lean_dec(x_45);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_47);
if (x_86 == 0)
{
lean_ctor_set_tag(x_47, 0);
return x_47;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_47, 0);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_47, 0);
lean_inc(x_89);
lean_dec(x_47);
x_90 = lean_mk_string_unchecked("id", 2, 2);
x_91 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262__spec__0(x_1, x_90);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
lean_dec(x_89);
lean_dec(x_45);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_95 = lean_mk_string_unchecked("Lean", 4, 4);
x_96 = lean_mk_string_unchecked("Lsp", 3, 3);
x_97 = lean_mk_string_unchecked("ResolvableCompletionItemData", 28, 28);
x_98 = l_Lean_Name_mkStr3(x_95, x_96, x_97);
x_99 = lean_box(1);
x_100 = lean_unbox(x_99);
lean_inc(x_94);
x_101 = l_Lean_Name_toString(x_98, x_100, x_94);
x_102 = lean_mk_string_unchecked(".", 1, 1);
x_103 = lean_string_append(x_101, x_102);
lean_dec(x_102);
x_104 = lean_mk_string_unchecked("id\?", 3, 3);
x_105 = l_Lean_Name_mkStr1(x_104);
x_106 = lean_unbox(x_99);
x_107 = l_Lean_Name_toString(x_105, x_106, x_94);
x_108 = lean_string_append(x_103, x_107);
lean_dec(x_107);
x_109 = lean_mk_string_unchecked(": ", 2, 2);
x_110 = lean_string_append(x_108, x_109);
lean_dec(x_109);
x_111 = lean_string_append(x_110, x_93);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_111);
return x_91;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
lean_dec(x_91);
x_113 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_114 = lean_mk_string_unchecked("Lean", 4, 4);
x_115 = lean_mk_string_unchecked("Lsp", 3, 3);
x_116 = lean_mk_string_unchecked("ResolvableCompletionItemData", 28, 28);
x_117 = l_Lean_Name_mkStr3(x_114, x_115, x_116);
x_118 = lean_box(1);
x_119 = lean_unbox(x_118);
lean_inc(x_113);
x_120 = l_Lean_Name_toString(x_117, x_119, x_113);
x_121 = lean_mk_string_unchecked(".", 1, 1);
x_122 = lean_string_append(x_120, x_121);
lean_dec(x_121);
x_123 = lean_mk_string_unchecked("id\?", 3, 3);
x_124 = l_Lean_Name_mkStr1(x_123);
x_125 = lean_unbox(x_118);
x_126 = l_Lean_Name_toString(x_124, x_125, x_113);
x_127 = lean_string_append(x_122, x_126);
lean_dec(x_126);
x_128 = lean_mk_string_unchecked(": ", 2, 2);
x_129 = lean_string_append(x_127, x_128);
lean_dec(x_128);
x_130 = lean_string_append(x_129, x_112);
lean_dec(x_112);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_132; 
lean_dec(x_89);
lean_dec(x_45);
x_132 = !lean_is_exclusive(x_91);
if (x_132 == 0)
{
lean_ctor_set_tag(x_91, 0);
return x_91;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_91, 0);
lean_inc(x_133);
lean_dec(x_91);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_91);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_91, 0);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_45);
lean_ctor_set(x_137, 1, x_89);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_91, 0, x_137);
return x_91;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_91, 0);
lean_inc(x_138);
lean_dec(x_91);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_45);
lean_ctor_set(x_139, 1, x_89);
lean_ctor_set(x_139, 2, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolvableCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_262_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_158_(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("params", 6, 6);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3059_(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("cPos", 4, 4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_JsonNumber_fromNat(x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_mk_string_unchecked("id", 2, 2);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Json_opt___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407__spec__0(x_14, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = l_List_flatMapTR_go___at_____private_Lean_Data_Lsp_Window_0__toJsonShowMessageParams____x40_Lean_Data_Lsp_Window___hyg_245__spec__0(x_20, x_22);
x_24 = l_Lean_Json_mkObj(x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonResolvableCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_2);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3_spec__3___redArg(x_8, x_11, x_9, x_16, x_18, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(120u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_format_pretty(x_9, x_10, x_11, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_unsigned_to_nat(120u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_format_pretty(x_13, x_15, x_16, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_163; lean_object* x_164; lean_object* x_174; 
x_21 = lean_st_ref_get(x_6, x_7);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__0), 1, 0);
x_55 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_158____boxed), 1, 0);
x_56 = lean_ctor_get(x_22, 0);
lean_inc(x_56);
lean_dec(x_22);
x_174 = lean_ctor_get(x_1, 1);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed), 6, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_2, 0);
lean_inc(x_186);
x_187 = lean_box(0);
x_188 = lean_unbox(x_187);
lean_inc(x_56);
x_189 = l_Lean_Environment_find_x3f(x_56, x_186, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_dec(x_175);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_163 = x_174;
x_164 = x_23;
goto block_173;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_Lean_ConstantInfo_type(x_190);
lean_dec(x_190);
x_176 = x_191;
goto block_185;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_2, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_3, 2);
lean_inc(x_193);
x_194 = lean_local_ctx_find(x_193, x_192);
if (lean_obj_tag(x_194) == 0)
{
lean_dec(x_175);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_163 = x_174;
x_164 = x_23;
goto block_173;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_ctor_get(x_195, 3);
lean_inc(x_196);
lean_dec(x_195);
x_176 = x_196;
goto block_185;
}
}
block_185:
{
lean_object* x_177; 
lean_inc(x_5);
x_177 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_176, x_175, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_178);
x_163 = x_180;
x_164 = x_179;
goto block_173;
}
else
{
uint8_t x_181; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_177);
if (x_181 == 0)
{
return x_177;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_177, 0);
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_177);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
else
{
lean_dec(x_174);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_79 = x_1;
x_80 = x_5;
x_81 = x_23;
goto block_162;
}
block_20:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 7);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_10);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_14);
lean_ctor_set(x_18, 5, x_15);
lean_ctor_set(x_18, 6, x_16);
lean_ctor_set(x_18, 7, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
block_34:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_mk_string_unchecked("\n\n", 2, 2);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_string_append(x_31, x_28);
lean_dec(x_28);
x_33 = l_Lean_Lsp_CompletionItem_resolve___lam__0(x_32);
x_8 = x_26;
x_9 = x_27;
x_10 = x_33;
goto block_20;
}
block_54:
{
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_36);
x_8 = x_38;
x_9 = x_40;
x_10 = x_35;
goto block_20;
}
else
{
lean_object* x_41; 
lean_dec(x_35);
x_41 = lean_apply_1(x_36, x_39);
x_8 = x_38;
x_9 = x_40;
x_10 = x_41;
goto block_20;
}
}
else
{
lean_dec(x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_apply_1(x_36, x_42);
x_8 = x_38;
x_9 = x_40;
x_10 = x_43;
goto block_20;
}
else
{
lean_object* x_44; 
lean_dec(x_36);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_mk_string_unchecked("none", 4, 4);
x_26 = x_38;
x_27 = x_40;
x_28 = x_45;
x_29 = x_46;
goto block_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_mk_string_unchecked("(some ", 6, 6);
x_50 = l_addParenHeuristic(x_48);
lean_dec(x_48);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked(")", 1, 1);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_26 = x_38;
x_27 = x_40;
x_28 = x_47;
x_29 = x_53;
goto block_34;
}
}
}
}
block_69:
{
lean_dec(x_57);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_dec(x_2);
x_65 = l_Lean_findDocString_x3f(x_56, x_64, x_62, x_60);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_35 = x_58;
x_36 = x_59;
x_37 = x_63;
x_38 = x_61;
x_39 = x_66;
x_40 = x_67;
goto block_54;
}
else
{
lean_object* x_68; 
lean_dec(x_56);
lean_dec(x_2);
x_68 = lean_box(0);
x_35 = x_58;
x_36 = x_59;
x_37 = x_63;
x_38 = x_61;
x_39 = x_68;
x_40 = x_60;
goto block_54;
}
}
block_78:
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_57 = x_70;
x_58 = x_71;
x_59 = x_72;
x_60 = x_73;
x_61 = x_74;
x_62 = x_75;
x_63 = x_77;
goto block_69;
}
block_162:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 2);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_24);
x_83 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__4___boxed), 3, 2);
lean_closure_set(x_83, 0, x_82);
lean_closure_set(x_83, 1, x_25);
x_84 = lean_box(1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
x_86 = l_Lean_Linter_instInhabitedDeprecationEntry;
x_87 = l_Lean_Linter_deprecatedAttr;
lean_inc(x_85);
lean_inc(x_56);
x_88 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_86, x_87, x_56, x_85);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
lean_dec(x_85);
lean_dec(x_55);
x_89 = lean_box(0);
x_90 = lean_unbox(x_84);
x_57 = x_80;
x_58 = x_82;
x_59 = x_83;
x_60 = x_81;
x_61 = x_79;
x_62 = x_90;
x_63 = x_89;
goto block_69;
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_95 = lean_mk_string_unchecked("`", 1, 1);
x_96 = lean_unbox(x_84);
x_97 = l_Lean_Name_toString(x_85, x_96, x_55);
x_98 = lean_string_append(x_95, x_97);
lean_dec(x_97);
x_99 = lean_mk_string_unchecked("` has been deprecated.", 22, 22);
x_100 = lean_string_append(x_98, x_99);
lean_dec(x_99);
lean_ctor_set(x_88, 0, x_100);
x_101 = lean_unbox(x_84);
x_70 = x_80;
x_71 = x_82;
x_72 = x_83;
x_73 = x_81;
x_74 = x_79;
x_75 = x_101;
x_76 = x_88;
goto block_78;
}
else
{
uint8_t x_102; 
lean_free_object(x_88);
x_102 = !lean_is_exclusive(x_94);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_103 = lean_ctor_get(x_94, 0);
x_104 = lean_mk_string_unchecked("`", 1, 1);
x_105 = lean_unbox(x_84);
lean_inc(x_55);
x_106 = l_Lean_Name_toString(x_85, x_105, x_55);
x_107 = lean_string_append(x_104, x_106);
lean_dec(x_106);
x_108 = lean_mk_string_unchecked("` has been deprecated, use `", 28, 28);
x_109 = lean_string_append(x_107, x_108);
lean_dec(x_108);
x_110 = lean_unbox(x_84);
x_111 = l_Lean_Name_toString(x_103, x_110, x_55);
x_112 = lean_string_append(x_109, x_111);
lean_dec(x_111);
x_113 = lean_mk_string_unchecked("` instead.", 10, 10);
x_114 = lean_string_append(x_112, x_113);
lean_dec(x_113);
lean_ctor_set(x_94, 0, x_114);
x_115 = lean_unbox(x_84);
x_70 = x_80;
x_71 = x_82;
x_72 = x_83;
x_73 = x_81;
x_74 = x_79;
x_75 = x_115;
x_76 = x_94;
goto block_78;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_116 = lean_ctor_get(x_94, 0);
lean_inc(x_116);
lean_dec(x_94);
x_117 = lean_mk_string_unchecked("`", 1, 1);
x_118 = lean_unbox(x_84);
lean_inc(x_55);
x_119 = l_Lean_Name_toString(x_85, x_118, x_55);
x_120 = lean_string_append(x_117, x_119);
lean_dec(x_119);
x_121 = lean_mk_string_unchecked("` has been deprecated, use `", 28, 28);
x_122 = lean_string_append(x_120, x_121);
lean_dec(x_121);
x_123 = lean_unbox(x_84);
x_124 = l_Lean_Name_toString(x_116, x_123, x_55);
x_125 = lean_string_append(x_122, x_124);
lean_dec(x_124);
x_126 = lean_mk_string_unchecked("` instead.", 10, 10);
x_127 = lean_string_append(x_125, x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_unbox(x_84);
x_70 = x_80;
x_71 = x_82;
x_72 = x_83;
x_73 = x_81;
x_74 = x_79;
x_75 = x_129;
x_76 = x_128;
goto block_78;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_92);
lean_dec(x_85);
lean_dec(x_55);
lean_ctor_set(x_88, 0, x_93);
x_130 = lean_unbox(x_84);
x_57 = x_80;
x_58 = x_82;
x_59 = x_83;
x_60 = x_81;
x_61 = x_79;
x_62 = x_130;
x_63 = x_88;
goto block_69;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_88, 0);
lean_inc(x_131);
lean_dec(x_88);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_134 = lean_mk_string_unchecked("`", 1, 1);
x_135 = lean_unbox(x_84);
x_136 = l_Lean_Name_toString(x_85, x_135, x_55);
x_137 = lean_string_append(x_134, x_136);
lean_dec(x_136);
x_138 = lean_mk_string_unchecked("` has been deprecated.", 22, 22);
x_139 = lean_string_append(x_137, x_138);
lean_dec(x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_unbox(x_84);
x_70 = x_80;
x_71 = x_82;
x_72 = x_83;
x_73 = x_81;
x_74 = x_79;
x_75 = x_141;
x_76 = x_140;
goto block_78;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_142 = lean_ctor_get(x_133, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_143 = x_133;
} else {
 lean_dec_ref(x_133);
 x_143 = lean_box(0);
}
x_144 = lean_mk_string_unchecked("`", 1, 1);
x_145 = lean_unbox(x_84);
lean_inc(x_55);
x_146 = l_Lean_Name_toString(x_85, x_145, x_55);
x_147 = lean_string_append(x_144, x_146);
lean_dec(x_146);
x_148 = lean_mk_string_unchecked("` has been deprecated, use `", 28, 28);
x_149 = lean_string_append(x_147, x_148);
lean_dec(x_148);
x_150 = lean_unbox(x_84);
x_151 = l_Lean_Name_toString(x_142, x_150, x_55);
x_152 = lean_string_append(x_149, x_151);
lean_dec(x_151);
x_153 = lean_mk_string_unchecked("` instead.", 10, 10);
x_154 = lean_string_append(x_152, x_153);
lean_dec(x_153);
if (lean_is_scalar(x_143)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_143;
}
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_unbox(x_84);
x_70 = x_80;
x_71 = x_82;
x_72 = x_83;
x_73 = x_81;
x_74 = x_79;
x_75 = x_156;
x_76 = x_155;
goto block_78;
}
}
else
{
lean_object* x_157; uint8_t x_158; 
lean_dec(x_131);
lean_dec(x_85);
lean_dec(x_55);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_132);
x_158 = lean_unbox(x_84);
x_57 = x_80;
x_58 = x_82;
x_59 = x_83;
x_60 = x_81;
x_61 = x_79;
x_62 = x_158;
x_63 = x_157;
goto block_69;
}
}
}
}
else
{
lean_object* x_159; uint8_t x_160; 
lean_dec(x_55);
x_159 = lean_box(0);
x_160 = lean_unbox(x_84);
x_57 = x_80;
x_58 = x_82;
x_59 = x_83;
x_60 = x_81;
x_61 = x_79;
x_62 = x_160;
x_63 = x_159;
goto block_69;
}
}
else
{
lean_object* x_161; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_25);
lean_dec(x_2);
if (lean_is_scalar(x_24)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_24;
}
lean_ctor_set(x_161, 0, x_79);
lean_ctor_set(x_161, 1, x_81);
return x_161;
}
}
block_173:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_1, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_1, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_1, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_1, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_1, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_1, 6);
lean_inc(x_170);
x_171 = lean_ctor_get(x_1, 7);
lean_inc(x_171);
lean_dec(x_1);
x_172 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_172, 0, x_165);
lean_ctor_set(x_172, 1, x_163);
lean_ctor_set(x_172, 2, x_166);
lean_ctor_set(x_172, 3, x_167);
lean_ctor_set(x_172, 4, x_168);
lean_ctor_set(x_172, 5, x_169);
lean_ctor_set(x_172, 6, x_170);
lean_ctor_set(x_172, 7, x_171);
x_79 = x_172;
x_80 = x_5;
x_81 = x_164;
goto block_162;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_CompletionItem_resolve___lam__4(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Lsp_CompletionItem_resolve___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Server_Completion_findCompletionInfosAt(x_1, x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_7, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_9);
x_15 = lean_array_fget(x_11, x_7);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_CompletionInfo_lctx(x_17);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve), 7, 2);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_6);
x_20 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_16, x_18, x_19, x_8);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_7, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_fget(x_21, x_7);
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_CompletionInfo_lctx(x_27);
lean_dec(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve), 7, 2);
lean_closure_set(x_29, 0, x_5);
lean_closure_set(x_29, 1, x_6);
x_30 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_26, x_28, x_29, x_8);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_Completion_resolveCompletionItem_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
lean_object* initialize_Lean_Server_Completion_CompletionItemData(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_CompletionItemData(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instFromJsonCompletionIdentifier = _init_l_Lean_Lsp_instFromJsonCompletionIdentifier();
lean_mark_persistent(l_Lean_Lsp_instFromJsonCompletionIdentifier);
l_Lean_Lsp_instToJsonCompletionIdentifier = _init_l_Lean_Lsp_instToJsonCompletionIdentifier();
lean_mark_persistent(l_Lean_Lsp_instToJsonCompletionIdentifier);
l_Lean_Lsp_instFromJsonResolvableCompletionItemData = _init_l_Lean_Lsp_instFromJsonResolvableCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instFromJsonResolvableCompletionItemData);
l_Lean_Lsp_instToJsonResolvableCompletionItemData = _init_l_Lean_Lsp_instToJsonResolvableCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instToJsonResolvableCompletionItemData);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
