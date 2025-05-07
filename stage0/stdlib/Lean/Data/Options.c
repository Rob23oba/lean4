// Lean compiler output
// Module: Lean.Data.Options
// Imports: Lean.ImportingFlag Lean.Data.KVMap Lean.Data.NameMap
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
LEAN_EXPORT lean_object* l___auto____x40_Lean_Data_Options___hyg_1083_;
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object*);
LEAN_EXPORT uint8_t l_Lean_registerOption___lam__0(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_registerOption;
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_instForInProdNameDataValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameMap_find_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringOptions;
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInOptionsProdNameDataValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_registerBuiltinOption;
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOptionDecls;
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_KVMap_instToString;
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedOptionDecl;
LEAN_EXPORT lean_object* l_Lean_instInhabitedOptions;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_149_(lean_object*);
lean_object* l_Lean_KVMap_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lean_get_option_decls_array(lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqOptions;
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OptionDecl_declName___autoParam;
LEAN_EXPORT lean_object* l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
uint8_t l_Lean_NameMap_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object*, lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_empty;
LEAN_EXPORT lean_object* l_Lean_registerOption___lam__0___boxed(lean_object*);
static lean_object* _init_l_Lean_Options_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedOptions() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringOptions() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_instToString;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInOptionsProdNameDataValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_KVMap_instForInProdNameDataValue(lean_box(0));
return x_2;
}
}
static lean_object* _init_l_Lean_instBEqOptions() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_eqv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_OptionDecl_declName___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("declName", 8, 8);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_20 = l_Lean_mkAtom(x_19);
lean_inc(x_7);
x_21 = lean_array_push(x_7, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedOptionDecls() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_149_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_registerOption___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_register_option(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_initializing(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_mk_string_unchecked("failed to register option, options can only be registered during initialization", 79, 79);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_mk_string_unchecked("failed to register option, options can only be registered during initialization", 79, 79);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
x_17 = lean_st_ref_get(x_16, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_NameMap_contains(lean_box(0), x_19, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_17);
x_22 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_19, x_1, x_2);
x_23 = lean_st_ref_set(x_16, x_22, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_19);
lean_dec(x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_registerOption___lam__0___boxed), 1, 0);
x_29 = lean_mk_string_unchecked("invalid option declaration '", 28, 28);
x_30 = l_Lean_Name_toString(x_1, x_21, x_28);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = lean_mk_string_unchecked("', option already exists", 24, 24);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_34);
return x_17;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = l_Lean_NameMap_contains(lean_box(0), x_35, x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_35, x_1, x_2);
x_39 = lean_st_ref_set(x_16, x_38, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_35);
lean_dec(x_2);
x_44 = lean_alloc_closure((void*)(l_Lean_registerOption___lam__0___boxed), 1, 0);
x_45 = lean_mk_string_unchecked("invalid option declaration '", 28, 28);
x_46 = l_Lean_Name_toString(x_1, x_37, x_44);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = lean_mk_string_unchecked("', option already exists", 24, 24);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_36);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerOption___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_registerOption___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l___private_Lean_Data_Options_0__Lean_optionDeclsRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lean_get_option_decls_array(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_getOptionDecls(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0(x_6, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0(x_11, x_8);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___Lean_getOptionDeclsArray_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_getOptionDecls(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_NameMap_find_x3f(lean_box(0), x_5, x_1);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_alloc_closure((void*)(l_Lean_registerOption___lam__0___boxed), 1, 0);
x_8 = lean_mk_string_unchecked("unknown option '", 16, 16);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Name_toString(x_1, x_10, x_7);
x_12 = lean_string_append(x_8, x_11);
lean_dec(x_11);
x_13 = lean_mk_string_unchecked("'", 1, 1);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = l_Lean_NameMap_find_x3f(lean_box(0), x_17, x_1);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_alloc_closure((void*)(l_Lean_registerOption___lam__0___boxed), 1, 0);
x_21 = lean_mk_string_unchecked("unknown option '", 16, 16);
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Name_toString(x_1, x_23, x_20);
x_25 = lean_string_append(x_21, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("'", 1, 1);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDefaultValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getOptionDescr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadOptionsOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_KVMap_getBool(x_4, x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_getBoolOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getBoolOption___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_getBoolOption___redArg___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_getBoolOption___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_getBoolOption(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_KVMap_getNat(x_4, x_1, x_2);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_getNatOption___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getNatOption___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getNatOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getNatOption___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__0), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_3(x_2, lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadWithOptionsOfMonadFunctor___redArg___lam__1), 5, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadWithOptionsOfMonadFunctor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instMonadWithOptionsOfMonadFunctor___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("_inPattern", 10, 10);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_KVMap_setBool(x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_withInPattern___redArg___lam__0), 1, 0);
x_4 = lean_apply_3(x_1, lean_box(0), x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withInPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_withInPattern___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Options_getInPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_mk_string_unchecked("_inPattern", 10, 10);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_KVMap_getBool(x_1, x_3, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_getInPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Options_getInPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_KVMap_findCore(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_1(x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_get_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_KVMap_findCore(x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_1);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_1(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Option_get___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_get(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_6, x_4);
x_8 = l_Lean_KVMap_insert(x_2, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Option_set___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_KVMap_contains(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Option_set___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Option_setIfNotSet___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___auto____x40_Lean_Data_Options___hyg_1083_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("declName", 8, 8);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_20 = l_Lean_mkAtom(x_19);
lean_inc(x_7);
x_21 = lean_array_push(x_7, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_7);
x_8 = lean_apply_1(x_6, x_7);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_inc(x_2);
x_12 = lean_register_option(x_2, x_11, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Option_register___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Option_registerBuiltinOption() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Option", 6, 6);
x_3 = lean_mk_string_unchecked("registerBuiltinOption", 21, 21);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("register_builtin_option", 23, 23);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_7);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("ident", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_7);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked(" : ", 3, 3);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_7);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked("term", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_27);
lean_inc(x_7);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_mk_string_unchecked(" := ", 4, 4);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_7);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
x_33 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerBuiltinOption__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Option", 6, 6);
x_6 = lean_mk_string_unchecked("registerBuiltinOption", 21, 21);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_115; lean_object* x_135; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(6u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_135 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_115 = x_136;
goto block_134;
}
else
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
x_115 = x_135;
goto block_134;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_115 = x_139;
goto block_134;
}
}
block_40:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_26);
lean_inc(x_29);
x_32 = l_Lean_Syntax_node2(x_29, x_26, x_31, x_18);
lean_inc(x_29);
x_33 = l_Lean_Syntax_node2(x_29, x_23, x_22, x_32);
lean_inc(x_29);
x_34 = l_Lean_Syntax_node1(x_29, x_28, x_33);
lean_inc(x_29);
x_35 = l_Lean_Syntax_node2(x_29, x_24, x_34, x_30);
lean_inc(x_29);
x_36 = l_Lean_Syntax_node1(x_29, x_26, x_35);
lean_inc(x_29);
x_37 = l_Lean_Syntax_node1(x_29, x_20, x_36);
x_38 = l_Lean_Syntax_node4(x_29, x_19, x_21, x_25, x_27, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
block_114:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_inc(x_44);
x_51 = l_Array_append(lean_box(0), x_44, x_50);
lean_dec(x_50);
lean_inc(x_46);
lean_inc(x_47);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_51);
lean_inc(x_46);
lean_inc(x_47);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_44);
lean_inc_n(x_53, 5);
lean_inc(x_47);
x_54 = l_Lean_Syntax_node6(x_47, x_49, x_52, x_53, x_53, x_53, x_53, x_53);
x_55 = lean_mk_string_unchecked("initializeKeyword", 17, 17);
lean_inc(x_42);
lean_inc(x_4);
x_56 = l_Lean_Name_mkStr4(x_4, x_42, x_43, x_55);
x_57 = lean_mk_string_unchecked("builtin_initialize", 18, 18);
lean_inc(x_47);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_57);
lean_inc(x_47);
x_59 = l_Lean_Syntax_node1(x_47, x_56, x_58);
x_60 = lean_mk_string_unchecked("Term", 4, 4);
x_61 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_60);
lean_inc(x_42);
lean_inc(x_4);
x_62 = l_Lean_Name_mkStr4(x_4, x_42, x_60, x_61);
x_63 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_47);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_60);
lean_inc(x_42);
lean_inc(x_4);
x_66 = l_Lean_Name_mkStr4(x_4, x_42, x_60, x_65);
x_67 = lean_mk_string_unchecked("Lean.Option", 11, 11);
x_68 = l_String_toSubstring_x27(x_67);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_Name_mkStr2(x_4, x_5);
lean_inc(x_48);
lean_inc(x_69);
lean_inc(x_45);
x_70 = l_Lean_addMacroScope(x_45, x_69, x_48);
x_71 = lean_box(0);
lean_inc(x_69);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_69);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_47);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_47);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_76);
lean_inc(x_46);
lean_inc(x_47);
x_78 = l_Lean_Syntax_node1(x_47, x_46, x_16);
lean_inc(x_66);
lean_inc(x_47);
x_79 = l_Lean_Syntax_node2(x_47, x_66, x_77, x_78);
lean_inc(x_47);
x_80 = l_Lean_Syntax_node2(x_47, x_62, x_64, x_79);
x_81 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_47);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_47);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_14);
lean_inc(x_46);
lean_inc(x_47);
x_83 = l_Lean_Syntax_node3(x_47, x_46, x_14, x_80, x_82);
x_84 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_60);
lean_inc(x_42);
lean_inc(x_4);
x_85 = l_Lean_Name_mkStr4(x_4, x_42, x_60, x_84);
x_86 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_60);
lean_inc(x_42);
lean_inc(x_4);
x_87 = l_Lean_Name_mkStr4(x_4, x_42, x_60, x_86);
x_88 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_60);
lean_inc(x_42);
lean_inc(x_4);
x_89 = l_Lean_Name_mkStr4(x_4, x_42, x_60, x_88);
x_90 = lean_mk_string_unchecked("Lean.Option.register", 20, 20);
x_91 = l_String_toSubstring_x27(x_90);
x_92 = lean_mk_string_unchecked("register", 8, 8);
lean_inc(x_4);
x_93 = l_Lean_Name_mkStr3(x_4, x_5, x_92);
lean_inc(x_93);
x_94 = l_Lean_addMacroScope(x_45, x_93, x_48);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_71);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_74);
lean_inc(x_47);
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_47);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_94);
lean_ctor_set(x_97, 3, x_96);
x_98 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
lean_inc(x_98);
x_99 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_71, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_60);
lean_dec(x_42);
lean_dec(x_4);
x_100 = l_Lean_quoteNameMk(x_98);
x_19 = x_41;
x_20 = x_85;
x_21 = x_54;
x_22 = x_97;
x_23 = x_66;
x_24 = x_87;
x_25 = x_59;
x_26 = x_46;
x_27 = x_83;
x_28 = x_89;
x_29 = x_47;
x_30 = x_53;
x_31 = x_100;
goto block_40;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_mk_string_unchecked("quotedName", 10, 10);
x_103 = l_Lean_Name_mkStr4(x_4, x_42, x_60, x_102);
x_104 = lean_mk_string_unchecked("`", 1, 1);
x_105 = lean_mk_string_unchecked(".", 1, 1);
x_106 = l_String_intercalate(x_105, x_101);
lean_dec(x_105);
x_107 = lean_string_append(x_104, x_106);
lean_dec(x_106);
x_108 = lean_box(2);
x_109 = l_Lean_Syntax_mkNameLit(x_107, x_108);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_mk_empty_array_with_capacity(x_110);
x_112 = lean_array_push(x_111, x_109);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_103);
lean_ctor_set(x_113, 2, x_112);
x_19 = x_41;
x_20 = x_85;
x_21 = x_54;
x_22 = x_97;
x_23 = x_66;
x_24 = x_87;
x_25 = x_59;
x_26 = x_46;
x_27 = x_83;
x_28 = x_89;
x_29 = x_47;
x_30 = x_53;
x_31 = x_113;
goto block_40;
}
}
block_134:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_116 = lean_ctor_get(x_2, 5);
lean_inc(x_116);
x_117 = lean_box(0);
x_118 = lean_unbox(x_117);
x_119 = l_Lean_SourceInfo_fromRef(x_116, x_118);
lean_dec(x_116);
x_120 = lean_ctor_get(x_2, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_2, 1);
lean_inc(x_121);
lean_dec(x_2);
x_122 = lean_mk_string_unchecked("Parser", 6, 6);
x_123 = lean_mk_string_unchecked("Command", 7, 7);
x_124 = lean_mk_string_unchecked("initialize", 10, 10);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_4);
x_125 = l_Lean_Name_mkStr4(x_4, x_122, x_123, x_124);
x_126 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_4);
x_127 = l_Lean_Name_mkStr4(x_4, x_122, x_123, x_126);
x_128 = lean_mk_string_unchecked("null", 4, 4);
x_129 = l_Lean_Name_mkStr1(x_128);
x_130 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_131; 
x_131 = l_Array_empty(lean_box(0));
x_41 = x_125;
x_42 = x_122;
x_43 = x_123;
x_44 = x_130;
x_45 = x_121;
x_46 = x_129;
x_47 = x_119;
x_48 = x_120;
x_49 = x_127;
x_50 = x_131;
goto block_114;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_115, 0);
lean_inc(x_132);
lean_dec(x_115);
x_133 = l_Array_mkArray1___redArg(x_132);
x_41 = x_125;
x_42 = x_122;
x_43 = x_123;
x_44 = x_130;
x_45 = x_121;
x_46 = x_129;
x_47 = x_119;
x_48 = x_120;
x_49 = x_127;
x_50 = x_133;
goto block_114;
}
}
}
}
}
static lean_object* _init_l_Lean_Option_registerOption() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Option", 6, 6);
x_3 = lean_mk_string_unchecked("registerOption", 14, 14);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("register_option", 15, 15);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_7);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("ident", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_7);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked(" : ", 3, 3);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_7);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked("term", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_27);
lean_inc(x_7);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_mk_string_unchecked(" := ", 4, 4);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_7);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
x_33 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_32);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Option___aux__Lean__Data__Options______macroRules__Lean__Option__registerOption__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Option", 6, 6);
x_6 = lean_mk_string_unchecked("registerOption", 14, 14);
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Name_mkStr3(x_4, x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_115; lean_object* x_135; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(6u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_135 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_115 = x_136;
goto block_134;
}
else
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
x_115 = x_135;
goto block_134;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_115 = x_139;
goto block_134;
}
}
block_40:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_21);
lean_inc(x_27);
x_32 = l_Lean_Syntax_node2(x_27, x_21, x_31, x_18);
lean_inc(x_27);
x_33 = l_Lean_Syntax_node2(x_27, x_29, x_25, x_32);
lean_inc(x_27);
x_34 = l_Lean_Syntax_node1(x_27, x_22, x_33);
lean_inc(x_27);
x_35 = l_Lean_Syntax_node2(x_27, x_24, x_34, x_30);
lean_inc(x_27);
x_36 = l_Lean_Syntax_node1(x_27, x_21, x_35);
lean_inc(x_27);
x_37 = l_Lean_Syntax_node1(x_27, x_28, x_36);
x_38 = l_Lean_Syntax_node4(x_27, x_20, x_23, x_19, x_26, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
block_114:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_inc(x_49);
x_52 = l_Array_append(lean_box(0), x_49, x_51);
lean_dec(x_51);
lean_inc(x_42);
lean_inc(x_50);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_42);
lean_ctor_set(x_53, 2, x_52);
lean_inc(x_42);
lean_inc(x_50);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_49);
lean_inc_n(x_54, 5);
lean_inc(x_50);
x_55 = l_Lean_Syntax_node6(x_50, x_45, x_53, x_54, x_54, x_54, x_54, x_54);
x_56 = lean_mk_string_unchecked("initializeKeyword", 17, 17);
lean_inc(x_43);
lean_inc(x_4);
x_57 = l_Lean_Name_mkStr4(x_4, x_43, x_44, x_56);
lean_inc(x_50);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_47);
lean_inc(x_50);
x_59 = l_Lean_Syntax_node1(x_50, x_57, x_58);
x_60 = lean_mk_string_unchecked("Term", 4, 4);
x_61 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_60);
lean_inc(x_43);
lean_inc(x_4);
x_62 = l_Lean_Name_mkStr4(x_4, x_43, x_60, x_61);
x_63 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_50);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_60);
lean_inc(x_43);
lean_inc(x_4);
x_66 = l_Lean_Name_mkStr4(x_4, x_43, x_60, x_65);
x_67 = lean_mk_string_unchecked("Lean.Option", 11, 11);
x_68 = l_String_toSubstring_x27(x_67);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_Name_mkStr2(x_4, x_5);
lean_inc(x_48);
lean_inc(x_69);
lean_inc(x_46);
x_70 = l_Lean_addMacroScope(x_46, x_69, x_48);
x_71 = lean_box(0);
lean_inc(x_69);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_69);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
lean_inc(x_50);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_50);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_70);
lean_ctor_set(x_77, 3, x_76);
lean_inc(x_42);
lean_inc(x_50);
x_78 = l_Lean_Syntax_node1(x_50, x_42, x_16);
lean_inc(x_66);
lean_inc(x_50);
x_79 = l_Lean_Syntax_node2(x_50, x_66, x_77, x_78);
lean_inc(x_50);
x_80 = l_Lean_Syntax_node2(x_50, x_62, x_64, x_79);
x_81 = lean_mk_string_unchecked("←", 3, 1);
lean_inc(x_50);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_50);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_14);
lean_inc(x_42);
lean_inc(x_50);
x_83 = l_Lean_Syntax_node3(x_50, x_42, x_14, x_80, x_82);
x_84 = lean_mk_string_unchecked("doSeqIndent", 11, 11);
lean_inc(x_60);
lean_inc(x_43);
lean_inc(x_4);
x_85 = l_Lean_Name_mkStr4(x_4, x_43, x_60, x_84);
x_86 = lean_mk_string_unchecked("doSeqItem", 9, 9);
lean_inc(x_60);
lean_inc(x_43);
lean_inc(x_4);
x_87 = l_Lean_Name_mkStr4(x_4, x_43, x_60, x_86);
x_88 = lean_mk_string_unchecked("doExpr", 6, 6);
lean_inc(x_60);
lean_inc(x_43);
lean_inc(x_4);
x_89 = l_Lean_Name_mkStr4(x_4, x_43, x_60, x_88);
x_90 = lean_mk_string_unchecked("Lean.Option.register", 20, 20);
x_91 = l_String_toSubstring_x27(x_90);
x_92 = lean_mk_string_unchecked("register", 8, 8);
lean_inc(x_4);
x_93 = l_Lean_Name_mkStr3(x_4, x_5, x_92);
lean_inc(x_93);
x_94 = l_Lean_addMacroScope(x_46, x_93, x_48);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_71);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_74);
lean_inc(x_50);
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_50);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_94);
lean_ctor_set(x_97, 3, x_96);
x_98 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
lean_inc(x_98);
x_99 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_71, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_60);
lean_dec(x_43);
lean_dec(x_4);
x_100 = l_Lean_quoteNameMk(x_98);
x_19 = x_59;
x_20 = x_41;
x_21 = x_42;
x_22 = x_89;
x_23 = x_55;
x_24 = x_87;
x_25 = x_97;
x_26 = x_83;
x_27 = x_50;
x_28 = x_85;
x_29 = x_66;
x_30 = x_54;
x_31 = x_100;
goto block_40;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_mk_string_unchecked("quotedName", 10, 10);
x_103 = l_Lean_Name_mkStr4(x_4, x_43, x_60, x_102);
x_104 = lean_mk_string_unchecked("`", 1, 1);
x_105 = lean_mk_string_unchecked(".", 1, 1);
x_106 = l_String_intercalate(x_105, x_101);
lean_dec(x_105);
x_107 = lean_string_append(x_104, x_106);
lean_dec(x_106);
x_108 = lean_box(2);
x_109 = l_Lean_Syntax_mkNameLit(x_107, x_108);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_mk_empty_array_with_capacity(x_110);
x_112 = lean_array_push(x_111, x_109);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_103);
lean_ctor_set(x_113, 2, x_112);
x_19 = x_59;
x_20 = x_41;
x_21 = x_42;
x_22 = x_89;
x_23 = x_55;
x_24 = x_87;
x_25 = x_97;
x_26 = x_83;
x_27 = x_50;
x_28 = x_85;
x_29 = x_66;
x_30 = x_54;
x_31 = x_113;
goto block_40;
}
}
block_134:
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_116 = lean_ctor_get(x_2, 5);
lean_inc(x_116);
x_117 = lean_box(0);
x_118 = lean_unbox(x_117);
x_119 = l_Lean_SourceInfo_fromRef(x_116, x_118);
lean_dec(x_116);
x_120 = lean_ctor_get(x_2, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_2, 1);
lean_inc(x_121);
lean_dec(x_2);
x_122 = lean_mk_string_unchecked("Parser", 6, 6);
x_123 = lean_mk_string_unchecked("Command", 7, 7);
x_124 = lean_mk_string_unchecked("initialize", 10, 10);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_4);
x_125 = l_Lean_Name_mkStr4(x_4, x_122, x_123, x_124);
x_126 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_4);
x_127 = l_Lean_Name_mkStr4(x_4, x_122, x_123, x_126);
x_128 = lean_mk_string_unchecked("null", 4, 4);
x_129 = l_Lean_Name_mkStr1(x_128);
x_130 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_131; 
x_131 = l_Array_empty(lean_box(0));
x_41 = x_125;
x_42 = x_129;
x_43 = x_122;
x_44 = x_123;
x_45 = x_127;
x_46 = x_121;
x_47 = x_124;
x_48 = x_120;
x_49 = x_130;
x_50 = x_119;
x_51 = x_131;
goto block_114;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_115, 0);
lean_inc(x_132);
lean_dec(x_115);
x_133 = l_Array_mkArray1___redArg(x_132);
x_41 = x_125;
x_42 = x_129;
x_43 = x_122;
x_44 = x_123;
x_45 = x_127;
x_46 = x_121;
x_47 = x_124;
x_48 = x_120;
x_49 = x_130;
x_50 = x_119;
x_51 = x_133;
goto block_114;
}
}
}
}
}
lean_object* initialize_Lean_ImportingFlag(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_NameMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ImportingFlag(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean_mark_persistent(l_Lean_Options_empty);
l_Lean_instInhabitedOptions = _init_l_Lean_instInhabitedOptions();
lean_mark_persistent(l_Lean_instInhabitedOptions);
l_Lean_instToStringOptions = _init_l_Lean_instToStringOptions();
lean_mark_persistent(l_Lean_instToStringOptions);
l_Lean_instBEqOptions = _init_l_Lean_instBEqOptions();
lean_mark_persistent(l_Lean_instBEqOptions);
l_Lean_OptionDecl_declName___autoParam = _init_l_Lean_OptionDecl_declName___autoParam();
lean_mark_persistent(l_Lean_OptionDecl_declName___autoParam);
l_Lean_instInhabitedOptionDecl = _init_l_Lean_instInhabitedOptionDecl();
lean_mark_persistent(l_Lean_instInhabitedOptionDecl);
l_Lean_instInhabitedOptionDecls = _init_l_Lean_instInhabitedOptionDecls();
lean_mark_persistent(l_Lean_instInhabitedOptionDecls);
if (builtin) {res = l_Lean_initFn____x40_Lean_Data_Options___hyg_149_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Data_Options_0__Lean_optionDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Data_Options_0__Lean_optionDeclsRef);
lean_dec_ref(res);
}l___auto____x40_Lean_Data_Options___hyg_1083_ = _init_l___auto____x40_Lean_Data_Options___hyg_1083_();
lean_mark_persistent(l___auto____x40_Lean_Data_Options___hyg_1083_);
l_Lean_Option_registerBuiltinOption = _init_l_Lean_Option_registerBuiltinOption();
lean_mark_persistent(l_Lean_Option_registerBuiltinOption);
l_Lean_Option_registerOption = _init_l_Lean_Option_registerOption();
lean_mark_persistent(l_Lean_Option_registerOption);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
