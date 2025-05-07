// Lean compiler output
// Module: Std.Data.HashMap.AdditionalOperations
// Imports: Std.Data.DHashMap.AdditionalOperations Std.Data.HashMap.Basic Std.Data.HashMap.Raw
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
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_map___redArg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_length___redArg(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filterMap), 5, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, lean_box(0));
lean_closure_set(x_6, 3, x_1);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_array_size(x_4);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
lean_inc(x_16);
x_20 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_16, x_6, x_17, x_19, x_4);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_18, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
else
{
lean_object* x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_alloc_closure((void*)(l_Std_HashMap_filterMap___redArg___lam__0___boxed), 2, 0);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
lean_inc(x_20);
x_26 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_16, x_24, x_20, x_19, x_25, x_18);
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filterMap), 5, 4);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, lean_box(0));
lean_closure_set(x_28, 2, lean_box(0));
lean_closure_set(x_28, 3, x_1);
x_29 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_30 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_31 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_32 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_33 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_34 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_35 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = lean_array_size(x_27);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_usize_of_nat(x_40);
lean_inc(x_38);
x_42 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_38, x_28, x_39, x_41, x_27);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_40, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_43, x_43);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_alloc_closure((void*)(l_Std_HashMap_filterMap___redArg___lam__0___boxed), 2, 0);
x_49 = lean_usize_of_nat(x_43);
lean_dec(x_43);
lean_inc(x_42);
x_50 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_38, x_48, x_42, x_41, x_49, x_40);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filterMap), 5, 4);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, lean_box(0));
lean_closure_set(x_11, 3, x_6);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_18 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_array_size(x_9);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
lean_inc(x_21);
x_25 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_21, x_11, x_22, x_24, x_9);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_23, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_21);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_26, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_21);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_29; size_t x_30; lean_object* x_31; 
x_29 = lean_alloc_closure((void*)(l_Std_HashMap_filterMap___redArg___lam__0___boxed), 2, 0);
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
lean_inc(x_25);
x_31 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_21, x_29, x_25, x_24, x_30, x_23);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_filterMap), 5, 4);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, lean_box(0));
lean_closure_set(x_33, 2, lean_box(0));
lean_closure_set(x_33, 3, x_6);
x_34 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_35 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_36 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_37 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_38 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_39 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_40 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_array_size(x_32);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_usize_of_nat(x_45);
lean_inc(x_43);
x_47 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_43, x_33, x_44, x_46, x_32);
x_48 = lean_array_get_size(x_47);
x_49 = lean_nat_dec_lt(x_45, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_43);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
else
{
lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_alloc_closure((void*)(l_Std_HashMap_filterMap___redArg___lam__0___boxed), 2, 0);
x_54 = lean_usize_of_nat(x_48);
lean_dec(x_48);
lean_inc(x_47);
x_55 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_43, x_53, x_47, x_46, x_54, x_45);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMap_filterMap___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filterMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_HashMap_filterMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_map), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, lean_box(0));
lean_closure_set(x_5, 3, x_1);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_array_size(x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_15, x_5, x_16, x_18, x_4);
lean_ctor_set(x_2, 1, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_map), 5, 4);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, lean_box(0));
lean_closure_set(x_22, 2, lean_box(0));
lean_closure_set(x_22, 3, x_1);
x_23 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_24 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_25 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_26 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_27 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_28 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_29 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_array_size(x_21);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_usize_of_nat(x_34);
x_36 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_32, x_22, x_33, x_35, x_21);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_map), 5, 4);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, lean_box(0));
lean_closure_set(x_10, 3, x_6);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_14 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_15 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_16 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_17 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_array_size(x_9);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
x_24 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_20, x_10, x_21, x_23, x_9);
lean_ctor_set(x_7, 1, x_24);
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_map), 5, 4);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
lean_closure_set(x_27, 2, lean_box(0));
lean_closure_set(x_27, 3, x_6);
x_28 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_29 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_30 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_31 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_32 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_33 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_34 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_array_size(x_26);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_usize_of_nat(x_39);
x_41 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_37, x_27, x_38, x_40, x_26);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_HashMap_map(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* initialize_Std_Data_DHashMap_AdditionalOperations(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_AdditionalOperations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_AdditionalOperations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
