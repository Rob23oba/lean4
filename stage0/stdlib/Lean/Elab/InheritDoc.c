// Lean compiler output
// Module: Lean.Elab.InheritDoc
// Imports: Lean.Elab.InfoTree.Main Lean.DocString.Extension
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Elab_InheritDoc___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Elab_InheritDoc___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Elab_InheritDoc___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__1(uint8_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
extern lean_object* l_Lean_docStringExt;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
uint8_t l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_162_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(x_1, x_2, x_8, x_9, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = l_Lean_docStringExt;
x_13 = l_String_removeLeadingSpaces(x_1);
x_14 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_12, x_11, x_2, x_13);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 3);
lean_inc(x_17);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_19);
x_20 = lean_ctor_get(x_9, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 7);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_7);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_st_ref_set(x_5, x_23, x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = l_Lean_docStringExt;
x_35 = l_String_removeLeadingSpaces(x_1);
x_36 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_34, x_33, x_2, x_35);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 3);
lean_inc(x_39);
x_40 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_ctor_get(x_31, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_31, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_31, 7);
lean_inc(x_45);
lean_dec(x_31);
x_46 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_42);
lean_ctor_set(x_46, 5, x_43);
lean_ctor_set(x_46, 6, x_44);
lean_ctor_set(x_46, 7, x_45);
x_47 = lean_st_ref_set(x_5, x_46, x_32);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
LEAN_EXPORT uint8_t l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Environment_getModuleIdxFor_x3f(x_9, x_1);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__0(x_2, x_1, x_11, x_3, x_4, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("invalid doc string, declaration '", 33, 33);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Name_toString(x_1, x_19, x_16);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("' is in an imported module", 26, 26);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 0, x_23);
x_24 = l_Lean_MessageData_ofFormat(x_10);
x_25 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_24, x_3, x_4, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
x_26 = lean_box(0);
x_27 = lean_alloc_closure((void*)(l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_mk_string_unchecked("invalid doc string, declaration '", 33, 33);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Name_toString(x_1, x_30, x_27);
x_32 = lean_string_append(x_28, x_31);
lean_dec(x_31);
x_33 = lean_mk_string_unchecked("' is in an imported module", 26, 26);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_MessageData_ofFormat(x_35);
x_37 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_36, x_3, x_4, x_8);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_warningAsError;
x_7 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_9, x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(2);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25(x_1, x_12, x_2, x_3, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("attribute cannot be erased", 26, 26);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_214; uint8_t x_215; uint8_t x_216; 
x_214 = lean_box(0);
x_215 = lean_unbox(x_214);
x_216 = l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_162_(x_6, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_mk_string_unchecked("invalid `[inherit_doc]` attribute, must be global", 49, 49);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
x_219 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_218, x_7, x_8, x_9);
lean_dec(x_8);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_mk_string_unchecked("Parser", 6, 6);
x_221 = lean_mk_string_unchecked("Attr", 4, 4);
x_222 = lean_mk_string_unchecked("simple", 6, 6);
x_223 = l_Lean_Name_mkStr4(x_2, x_220, x_221, x_222);
lean_inc(x_5);
x_224 = l_Lean_Syntax_isOfKind(x_5, x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_225 = lean_mk_string_unchecked("invalid `[inherit_doc]` attribute", 33, 33);
x_226 = l_Lean_stringToMessageData(x_225);
lean_dec(x_225);
x_227 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_226, x_7, x_8, x_9);
lean_dec(x_8);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_unsigned_to_nat(0u);
x_229 = l_Lean_Syntax_getArg(x_5, x_228);
x_230 = l_Lean_Syntax_matchesIdent(x_229, x_3);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_229);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_231 = lean_mk_string_unchecked("invalid `[inherit_doc]` attribute", 33, 33);
x_232 = l_Lean_stringToMessageData(x_231);
lean_dec(x_231);
x_233 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_232, x_7, x_8, x_9);
lean_dec(x_8);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_unsigned_to_nat(1u);
x_235 = l_Lean_Syntax_getArg(x_5, x_234);
lean_dec(x_5);
x_236 = l_Lean_Syntax_isNone(x_235);
if (x_236 == 0)
{
uint8_t x_237; 
lean_inc(x_235);
x_237 = l_Lean_Syntax_matchesNull(x_235, x_234);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_235);
lean_dec(x_229);
lean_dec(x_4);
lean_dec(x_1);
x_238 = lean_mk_string_unchecked("invalid `[inherit_doc]` attribute", 33, 33);
x_239 = l_Lean_stringToMessageData(x_238);
lean_dec(x_238);
x_240 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_239, x_7, x_8, x_9);
lean_dec(x_8);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_241 = l_Lean_Syntax_getArg(x_235, x_228);
lean_dec(x_235);
x_242 = lean_mk_string_unchecked("ident", 5, 5);
x_243 = l_Lean_Name_mkStr1(x_242);
lean_inc(x_241);
x_244 = l_Lean_Syntax_isOfKind(x_241, x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_241);
lean_dec(x_229);
lean_dec(x_4);
lean_dec(x_1);
x_245 = lean_mk_string_unchecked("invalid `[inherit_doc]` attribute", 33, 33);
x_246 = l_Lean_stringToMessageData(x_245);
lean_dec(x_245);
x_247 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_246, x_7, x_8, x_9);
lean_dec(x_8);
return x_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_241);
x_95 = x_229;
x_96 = x_230;
x_97 = x_248;
x_98 = x_7;
x_99 = x_8;
x_100 = x_9;
goto block_213;
}
}
}
else
{
lean_object* x_249; 
lean_dec(x_235);
x_249 = lean_box(0);
x_95 = x_229;
x_96 = x_230;
x_97 = x_249;
x_98 = x_7;
x_99 = x_8;
x_100 = x_9;
goto block_213;
}
}
}
}
block_94:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_get(x_14, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_14);
lean_inc(x_13);
x_20 = lean_apply_4(x_1, x_18, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_10);
x_23 = l_Lean_findSimpleDocString_x3f(x_21, x_10, x_12, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(x_10, x_13, x_14, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_mk_string_unchecked("", 0, 0);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = l_Lean_MessageData_ofExpr(x_29);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_33);
lean_ctor_set(x_23, 0, x_32);
x_34 = lean_mk_string_unchecked(" does not have a doc string", 27, 27);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_35);
lean_ctor_set(x_16, 0, x_23);
x_36 = l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0(x_11, x_16, x_13, x_14, x_30);
lean_dec(x_14);
lean_dec(x_11);
return x_36;
}
else
{
uint8_t x_37; 
lean_free_object(x_23);
lean_free_object(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(x_10, x_13, x_14, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_mk_string_unchecked("", 0, 0);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = l_Lean_MessageData_ofExpr(x_43);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked(" does not have a doc string", 27, 27);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_50);
lean_ctor_set(x_16, 0, x_48);
x_51 = l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0(x_11, x_16, x_13, x_14, x_44);
lean_dec(x_14);
lean_dec(x_11);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_16);
lean_dec(x_11);
lean_dec(x_10);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_dec(x_23);
x_57 = lean_ctor_get(x_24, 0);
lean_inc(x_57);
lean_dec(x_24);
x_58 = l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1(x_4, x_57, x_13, x_14, x_56);
lean_dec(x_14);
lean_dec(x_13);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_20);
if (x_59 == 0)
{
return x_20;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_20, 0);
x_61 = lean_ctor_get(x_20, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_20);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_16, 0);
x_64 = lean_ctor_get(x_16, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_16);
lean_inc(x_14);
lean_inc(x_13);
x_65 = lean_apply_4(x_1, x_63, x_13, x_14, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_10);
x_68 = l_Lean_findSimpleDocString_x3f(x_66, x_10, x_12, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(x_10, x_13, x_14, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = l_Lean_MessageData_ofExpr(x_73);
if (lean_is_scalar(x_71)) {
 x_78 = lean_alloc_ctor(7, 2, 0);
} else {
 x_78 = x_71;
 lean_ctor_set_tag(x_78, 7);
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked(" does not have a doc string", 27, 27);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0(x_11, x_81, x_13, x_14, x_74);
lean_dec(x_14);
lean_dec(x_11);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_71);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_85 = x_72;
} else {
 lean_dec_ref(x_72);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_11);
lean_dec(x_10);
x_87 = lean_ctor_get(x_68, 1);
lean_inc(x_87);
lean_dec(x_68);
x_88 = lean_ctor_get(x_69, 0);
lean_inc(x_88);
lean_dec(x_69);
x_89 = l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1(x_4, x_88, x_13, x_14, x_87);
lean_dec(x_14);
lean_dec(x_13);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_90 = lean_ctor_get(x_65, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_65, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_92 = x_65;
} else {
 lean_dec_ref(x_65);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
block_213:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_101 = lean_ctor_get(x_98, 5);
x_102 = l_Lean_replaceRef(x_95, x_101);
lean_dec(x_95);
x_103 = lean_ctor_get(x_98, 0);
x_104 = lean_ctor_get(x_98, 1);
x_105 = lean_ctor_get(x_98, 2);
x_106 = lean_ctor_get(x_98, 3);
x_107 = lean_ctor_get(x_98, 4);
x_108 = lean_ctor_get(x_98, 6);
x_109 = lean_ctor_get(x_98, 7);
x_110 = lean_ctor_get(x_98, 8);
x_111 = lean_ctor_get(x_98, 9);
x_112 = lean_ctor_get(x_98, 10);
x_113 = lean_ctor_get_uint8(x_98, sizeof(void*)*13);
x_114 = lean_ctor_get(x_98, 11);
x_115 = lean_ctor_get_uint8(x_98, sizeof(void*)*13 + 1);
x_116 = lean_ctor_get(x_98, 12);
lean_inc(x_116);
lean_inc(x_114);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
x_117 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_104);
lean_ctor_set(x_117, 2, x_105);
lean_ctor_set(x_117, 3, x_106);
lean_ctor_set(x_117, 4, x_107);
lean_ctor_set(x_117, 5, x_102);
lean_ctor_set(x_117, 6, x_108);
lean_ctor_set(x_117, 7, x_109);
lean_ctor_set(x_117, 8, x_110);
lean_ctor_set(x_117, 9, x_111);
lean_ctor_set(x_117, 10, x_112);
lean_ctor_set(x_117, 11, x_114);
lean_ctor_set(x_117, 12, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*13, x_113);
lean_ctor_set_uint8(x_117, sizeof(void*)*13 + 1, x_115);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_4);
lean_dec(x_1);
x_118 = lean_mk_string_unchecked("invalid `[inherit_doc]` attribute, could not infer doc source", 61, 61);
x_119 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
x_120 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_119, x_117, x_99, x_100);
lean_dec(x_99);
lean_dec(x_117);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_97, 0);
lean_inc(x_121);
lean_dec(x_97);
x_122 = lean_box(0);
lean_inc(x_99);
lean_inc(x_117);
lean_inc(x_121);
x_123 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_121, x_122, x_117, x_99, x_100);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_st_ref_get(x_99, x_125);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_1);
lean_inc(x_99);
lean_inc(x_117);
x_130 = lean_apply_4(x_1, x_128, x_117, x_99, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_box(0);
x_134 = lean_unbox(x_133);
lean_inc(x_4);
x_135 = l_Lean_findSimpleDocString_x3f(x_131, x_4, x_134, x_132);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
lean_free_object(x_126);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_10 = x_124;
x_11 = x_121;
x_12 = x_96;
x_13 = x_117;
x_14 = x_99;
x_15 = x_137;
goto block_94;
}
else
{
lean_dec(x_136);
if (x_96 == 0)
{
lean_object* x_138; 
lean_free_object(x_126);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_10 = x_124;
x_11 = x_121;
x_12 = x_96;
x_13 = x_117;
x_14 = x_99;
x_15 = x_138;
goto block_94;
}
else
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_135);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_135, 1);
x_141 = lean_ctor_get(x_135, 0);
lean_dec(x_141);
lean_inc(x_4);
x_142 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(x_4, x_117, x_99, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_mk_string_unchecked("", 0, 0);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = l_Lean_MessageData_ofExpr(x_143);
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_147);
lean_ctor_set(x_135, 0, x_146);
x_148 = lean_mk_string_unchecked(" already has a doc string", 25, 25);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
lean_ctor_set_tag(x_126, 7);
lean_ctor_set(x_126, 1, x_149);
lean_ctor_set(x_126, 0, x_135);
lean_inc(x_117);
x_150 = l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2(x_126, x_117, x_99, x_144);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_10 = x_124;
x_11 = x_121;
x_12 = x_96;
x_13 = x_117;
x_14 = x_99;
x_15 = x_151;
goto block_94;
}
else
{
uint8_t x_152; 
lean_free_object(x_135);
lean_free_object(x_126);
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_4);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_142);
if (x_152 == 0)
{
return x_142;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_142, 0);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_142);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_135, 1);
lean_inc(x_156);
lean_dec(x_135);
lean_inc(x_4);
x_157 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(x_4, x_117, x_99, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_mk_string_unchecked("", 0, 0);
x_161 = l_Lean_stringToMessageData(x_160);
lean_dec(x_160);
x_162 = l_Lean_MessageData_ofExpr(x_158);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_mk_string_unchecked(" already has a doc string", 25, 25);
x_165 = l_Lean_stringToMessageData(x_164);
lean_dec(x_164);
lean_ctor_set_tag(x_126, 7);
lean_ctor_set(x_126, 1, x_165);
lean_ctor_set(x_126, 0, x_163);
lean_inc(x_117);
x_166 = l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2(x_126, x_117, x_99, x_159);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_10 = x_124;
x_11 = x_121;
x_12 = x_96;
x_13 = x_117;
x_14 = x_99;
x_15 = x_167;
goto block_94;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_free_object(x_126);
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_4);
lean_dec(x_1);
x_168 = lean_ctor_get(x_157, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_157, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_170 = x_157;
} else {
 lean_dec_ref(x_157);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
}
else
{
uint8_t x_172; 
lean_free_object(x_126);
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_4);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_130);
if (x_172 == 0)
{
return x_130;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_130, 0);
x_174 = lean_ctor_get(x_130, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_130);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_126, 0);
x_177 = lean_ctor_get(x_126, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_126);
lean_inc(x_1);
lean_inc(x_99);
lean_inc(x_117);
x_178 = lean_apply_4(x_1, x_176, x_117, x_99, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_box(0);
x_182 = lean_unbox(x_181);
lean_inc(x_4);
x_183 = l_Lean_findSimpleDocString_x3f(x_179, x_4, x_182, x_180);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_10 = x_124;
x_11 = x_121;
x_12 = x_96;
x_13 = x_117;
x_14 = x_99;
x_15 = x_185;
goto block_94;
}
else
{
lean_dec(x_184);
if (x_96 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_10 = x_124;
x_11 = x_121;
x_12 = x_96;
x_13 = x_117;
x_14 = x_99;
x_15 = x_186;
goto block_94;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_188 = x_183;
} else {
 lean_dec_ref(x_183);
 x_188 = lean_box(0);
}
lean_inc(x_4);
x_189 = l_Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0(x_4, x_117, x_99, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_mk_string_unchecked("", 0, 0);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
x_194 = l_Lean_MessageData_ofExpr(x_190);
if (lean_is_scalar(x_188)) {
 x_195 = lean_alloc_ctor(7, 2, 0);
} else {
 x_195 = x_188;
 lean_ctor_set_tag(x_195, 7);
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_mk_string_unchecked(" already has a doc string", 25, 25);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
lean_inc(x_117);
x_199 = l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2(x_198, x_117, x_99, x_191);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_10 = x_124;
x_11 = x_121;
x_12 = x_96;
x_13 = x_117;
x_14 = x_99;
x_15 = x_200;
goto block_94;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_188);
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_4);
lean_dec(x_1);
x_201 = lean_ctor_get(x_189, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_189, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_203 = x_189;
} else {
 lean_dec_ref(x_189);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_4);
lean_dec(x_1);
x_205 = lean_ctor_get(x_178, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_178, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_207 = x_178;
} else {
 lean_dec_ref(x_178);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_99);
lean_dec(x_4);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_123);
if (x_209 == 0)
{
return x_123;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_123, 0);
x_211 = lean_ctor_get(x_123, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_123);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_Elab_InheritDoc___hyg_3____boxed), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_initFn___lam__1____x40_Lean_Elab_InheritDoc___hyg_3____boxed), 4, 0);
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_5);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("initFn", 6, 6);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("_@", 2, 2);
x_10 = l_Lean_Name_str___override(x_8, x_9);
lean_inc(x_5);
x_11 = l_Lean_Name_str___override(x_10, x_5);
x_12 = lean_mk_string_unchecked("Elab", 4, 4);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("InheritDoc", 10, 10);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("_hyg", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Name_num___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("inherit_doc", 11, 11);
x_21 = l_Lean_Name_mkStr1(x_20);
lean_inc(x_21);
x_22 = lean_alloc_closure((void*)(l_Lean_initFn___lam__2____x40_Lean_Elab_InheritDoc___hyg_3____boxed), 9, 3);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("inherit documentation from a specified declaration", 50, 50);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_23);
x_26 = lean_unbox(x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_26);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_2);
x_28 = l_Lean_registerBuiltinAttribute(x_27, x_1);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDocStringCore___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logWarning___at___Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3__spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Elab_InheritDoc___hyg_3____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn___lam__0____x40_Lean_Elab_InheritDoc___hyg_3_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Elab_InheritDoc___hyg_3____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn___lam__1____x40_Lean_Elab_InheritDoc___hyg_3_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2____x40_Lean_Elab_InheritDoc___hyg_3____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_initFn___lam__2____x40_Lean_Elab_InheritDoc___hyg_3_(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_7);
return x_11;
}
}
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InheritDoc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_Elab_InheritDoc___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
