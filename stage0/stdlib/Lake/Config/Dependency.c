// Lean compiler output
// Module: Lake.Config.Dependency
// Imports: Init.Dynamic Init.System.FilePath Lean.Data.NameMap
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
LEAN_EXPORT lean_object* l_Lake_instInhabitedDependencySrc;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedDependency;
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Dependency_fullName___lam__0(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc;
LEAN_EXPORT lean_object* l___private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instImpl____x40_Lake_Config_Dependency___hyg_236_;
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instTypeNameDependency;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53_(lean_object*, lean_object*);
static lean_object* _init_l_Lake_instInhabitedDependencySrc() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("none", 4, 4);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_mk_string_unchecked("some ", 5, 5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_7);
x_8 = l_String_quote(x_6);
lean_dec(x_6);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Repr_addAppParen(x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("some ", 5, 5);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_String_quote(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_string_unchecked("none", 4, 4);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_mk_string_unchecked("some ", 5, 5);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_7);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_String_quote(x_6);
lean_dec(x_6);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Repr_addAppParen(x_13, x_8);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_mk_string_unchecked("some ", 5, 5);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(1024u);
x_21 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_String_quote(x_17);
lean_dec(x_17);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Repr_addAppParen(x_25, x_20);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Repr_addAppParen(x_27, x_2);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_24; uint8_t x_25; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_to_int(x_26);
x_5 = x_27;
goto block_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_to_int(x_28);
x_5 = x_29;
goto block_23;
}
block_23:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_6 = lean_mk_string_unchecked("Lake.DependencySrc.path", 23, 23);
if (lean_is_scalar(x_4)) {
 x_7 = lean_alloc_ctor(3, 1, 0);
} else {
 x_7 = x_4;
 lean_ctor_set_tag(x_7, 3);
}
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_String_quote(x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Repr_addAppParen(x_15, x_10);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = l_Repr_addAppParen(x_20, x_2);
return x_22;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_54; uint8_t x_55; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_54 = lean_unsigned_to_nat(1024u);
x_55 = lean_nat_dec_le(x_54, x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_nat_to_int(x_56);
x_33 = x_57;
goto block_53;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_to_int(x_58);
x_33 = x_59;
goto block_53;
}
block_53:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_34 = lean_mk_string_unchecked("Lake.DependencySrc.git", 22, 22);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(1);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_String_quote(x_30);
lean_dec(x_30);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
x_42 = lean_unsigned_to_nat(1024u);
x_43 = l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__0(x_31, x_42);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
x_46 = l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__1(x_32, x_42);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_unbox(x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_51);
x_52 = l_Repr_addAppParen(x_50, x_2);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_repr___at_____private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53__spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprDependencySrc() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_Dependency_0__Lake_reprDependencySrc____x40_Lake_Config_Dependency___hyg_53____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedDependency() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instImpl____x40_Lake_Config_Dependency___hyg_236_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("Dependency", 10, 10);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instTypeNameDependency() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instImpl____x40_Lake_Config_Dependency___hyg_236_;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Dependency_fullName___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_alloc_closure((void*)(l_Lake_Dependency_fullName___lam__0___boxed), 1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_mk_string_unchecked("/", 1, 1);
x_5 = lean_string_append(x_3, x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Name_toString(x_6, x_8, x_2);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Dependency_fullName___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init_Dynamic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_NameMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedDependencySrc = _init_l_Lake_instInhabitedDependencySrc();
lean_mark_persistent(l_Lake_instInhabitedDependencySrc);
l_Lake_instReprDependencySrc = _init_l_Lake_instReprDependencySrc();
lean_mark_persistent(l_Lake_instReprDependencySrc);
l_Lake_instInhabitedDependency = _init_l_Lake_instInhabitedDependency();
lean_mark_persistent(l_Lake_instInhabitedDependency);
l_Lake_instImpl____x40_Lake_Config_Dependency___hyg_236_ = _init_l_Lake_instImpl____x40_Lake_Config_Dependency___hyg_236_();
lean_mark_persistent(l_Lake_instImpl____x40_Lake_Config_Dependency___hyg_236_);
l_Lake_instTypeNameDependency = _init_l_Lake_instTypeNameDependency();
lean_mark_persistent(l_Lake_instTypeNameDependency);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
