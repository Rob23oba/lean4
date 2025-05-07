// Lean compiler output
// Module: Lake.Config.Dynlib
// Imports: Lake.Config.OutFormat Lake.Build.Target.Basic
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
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib;
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg____x40_Lake_Config_Dynlib___hyg_60_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDynlib;
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDynlibFilePath;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedDynlib;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg___lam__0____x40_Lake_Config_Dynlib___hyg_60_(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib____x40_Lake_Config_Dynlib___hyg_60____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib____x40_Lake_Config_Dynlib___hyg_60_(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib___lam__0(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib___lam__0___boxed(lean_object*);
static lean_object* _init_l_Lake_instInhabitedDynlib() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = lean_mk_string_unchecked("", 0, 0);
x_2 = lean_box(0);
x_3 = l_Array_empty(lean_box(0));
lean_inc(x_1);
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_5);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg___lam__0____x40_Lake_Config_Dynlib___hyg_60_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg____x40_Lake_Config_Dynlib___hyg_60_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg____x40_Lake_Config_Dynlib___hyg_60_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_97; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("path", 4, 4);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg___lam__0____x40_Lake_Config_Dynlib___hyg_60_), 1, 0);
x_15 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_String_quote(x_12);
lean_dec(x_12);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Repr_addAppParen(x_19, x_13);
lean_inc(x_11);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_21);
x_41 = lean_unbox(x_22);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_41);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_mk_string_unchecked(",", 1, 1);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_44);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("name", 4, 4);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_8);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = l_String_quote(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_11);
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_11);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_unbox(x_22);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_56);
lean_inc(x_44);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_44);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_46);
x_61 = lean_mk_string_unchecked("plugin", 6, 6);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
lean_inc(x_8);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_8);
x_65 = lean_unsigned_to_nat(10u);
x_66 = lean_nat_to_int(x_65);
x_97 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_mk_string_unchecked("false", 5, 5);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_67 = x_99;
goto block_96;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_mk_string_unchecked("true", 4, 4);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_67 = x_101;
goto block_96;
}
block_39:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_unbox(x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_mk_string_unchecked(" }", 2, 2);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_to_int(x_30);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_2);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_unbox(x_22);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
return x_37;
}
block_96:
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_unbox(x_22);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_70);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
lean_inc(x_44);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_44);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_46);
x_74 = lean_mk_string_unchecked("deps", 4, 4);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_8);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
lean_dec(x_1);
x_79 = lean_array_get_size(x_78);
x_80 = lean_nat_dec_eq(x_79, x_13);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_mk_string_unchecked("#[", 2, 2);
x_82 = lean_array_to_list(x_78);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_44);
lean_ctor_set(x_83, 1, x_46);
x_84 = l_Std_Format_joinSep(lean_box(0), x_14, x_82, x_83);
x_85 = lean_mk_string_unchecked("]", 1, 1);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_to_int(x_86);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_81);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Std_Format_fill(x_92);
x_23 = x_77;
x_24 = x_93;
goto block_39;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_78);
lean_dec(x_44);
lean_dec(x_14);
x_94 = lean_mk_string_unchecked("#[]", 3, 3);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_23 = x_77;
x_24 = x_95;
goto block_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib____x40_Lake_Config_Dynlib___hyg_60_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Dynlib_0__Lake_reprDynlib___redArg____x40_Lake_Config_Dynlib___hyg_60_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Dynlib_0__Lake_reprDynlib____x40_Lake_Config_Dynlib___hyg_60____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Dynlib_0__Lake_reprDynlib____x40_Lake_Config_Dynlib___hyg_60_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprDynlib() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_Dynlib_0__Lake_reprDynlib____x40_Lake_Config_Dynlib___hyg_60____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_System_FilePath_parent(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dynlib_dir_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Dynlib_dir_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_instToTextDynlib() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToTextDynlib___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToTextDynlib___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToTextDynlib___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonDynlib() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonDynlib___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonDynlib___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instToJsonDynlib___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instCoeDynlibFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToTextDynlib___lam__0___boxed), 1, 0);
return x_1;
}
}
lean_object* initialize_Lake_Config_OutFormat(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Target_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_OutFormat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Target_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedDynlib = _init_l_Lake_instInhabitedDynlib();
lean_mark_persistent(l_Lake_instInhabitedDynlib);
l_Lake_instReprDynlib = _init_l_Lake_instReprDynlib();
lean_mark_persistent(l_Lake_instReprDynlib);
l_Lake_instToTextDynlib = _init_l_Lake_instToTextDynlib();
lean_mark_persistent(l_Lake_instToTextDynlib);
l_Lake_instToJsonDynlib = _init_l_Lake_instToJsonDynlib();
lean_mark_persistent(l_Lake_instToJsonDynlib);
l_Lake_instCoeDynlibFilePath = _init_l_Lake_instCoeDynlibFilePath();
lean_mark_persistent(l_Lake_instCoeDynlibFilePath);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
