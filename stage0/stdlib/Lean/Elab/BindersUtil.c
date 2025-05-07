// Lean compiler output
// Module: Lean.Elab.BindersUtil
// Imports: Lean.Parser.Term
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_clearInMatch_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlt_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isNone(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_mkHole(x_1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandOptType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_expandOptType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArg(x_3, x_2);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Syntax_getArg(x_6, x_2);
lean_dec(x_6);
x_8 = l_Lean_Syntax_getSepArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMatchAltsNumPatterns___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getMatchAltsNumPatterns(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
x_15 = l_Lean_Syntax_getArg(x_1, x_13);
x_16 = lean_box(0);
lean_inc(x_4);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = lean_ctor_get(x_5, 5);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_20);
x_22 = lean_mk_string_unchecked("|", 1, 1);
lean_inc(x_21);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("null", 4, 4);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Array_mkArray0(lean_box(0));
x_27 = lean_array_uget(x_4, x_3);
lean_dec(x_4);
x_28 = l_Array_append(lean_box(0), x_26, x_27);
lean_dec(x_27);
lean_inc(x_25);
lean_inc(x_21);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_21);
x_30 = l_Lean_Syntax_node1(x_21, x_25, x_29);
x_31 = lean_mk_string_unchecked("=>", 2, 2);
lean_inc(x_21);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Syntax_node4(x_21, x_14, x_23, x_30, x_32, x_15);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_usize_of_nat(x_34);
x_36 = lean_usize_add(x_3, x_35);
x_37 = lean_array_uset(x_17, x_3, x_33);
x_3 = x_36;
x_4 = x_37;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlt_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Term", 4, 4);
x_15 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_16 = lean_usize_dec_eq(x_3, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_21 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_22 = l_Lean_Syntax_isOfKind(x_1, x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
lean_ctor_set(x_5, 0, x_23);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
lean_inc(x_1);
x_26 = l_Lean_Syntax_isOfKind(x_1, x_25);
lean_dec(x_25);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_6 = x_28;
goto block_11;
}
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = lean_array_uget(x_2, x_3);
x_33 = lean_array_push(x_30, x_32);
x_34 = lean_box(x_16);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_34);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_array_uget(x_2, x_3);
x_37 = lean_array_push(x_35, x_36);
x_38 = lean_box(x_16);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_6 = x_39;
goto block_11;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_array_push(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_14 = lean_unsigned_to_nat(1u);
x_29 = l_Lean_Syntax_getArg(x_1, x_14);
x_30 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_31 = l_Array_empty(lean_box(0));
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_30);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
x_15 = x_31;
goto block_28;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_33, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
x_15 = x_31;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_box(x_9);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
x_38 = lean_usize_of_nat(x_32);
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
lean_inc(x_1);
x_40 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlt_spec__2(x_1, x_30, x_38, x_39, x_37);
lean_dec(x_30);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_15 = x_41;
goto block_28;
}
}
block_28:
{
size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_array_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__0(x_16, x_18, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_le(x_21, x_14);
lean_dec(x_21);
if (x_22 == 0)
{
size_t x_23; lean_object* x_24; 
x_23 = lean_array_size(x_20);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__1(x_1, x_23, x_18, x_20, x_2, x_3);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_25 = lean_mk_empty_array_with_capacity(x_14);
x_26 = lean_array_push(x_25, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlt_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlt_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMatchAlt(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_shouldExpandMatchAlt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Term", 4, 4);
x_5 = lean_mk_string_unchecked("matchAlt", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_8 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_8);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = l_Array_empty(lean_box(0));
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_19);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_1);
x_9 = x_20;
goto block_17;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_1);
x_9 = x_20;
goto block_17;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_box(x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = lean_usize_of_nat(x_21);
x_28 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlt_spec__2(x_1, x_19, x_27, x_28, x_26);
lean_dec(x_19);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_9 = x_30;
goto block_17;
}
}
block_17:
{
size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_array_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_expandMatchAlt_spec__0(x_10, x_12, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_nat_dec_lt(x_8, x_15);
lean_dec(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_shouldExpandMatchAlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_shouldExpandMatchAlt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Term_shouldExpandMatchAlt(x_5);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_1, x_2);
x_16 = l_Lean_Elab_Term_expandMatchAlt(x_15, x_5, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_append(lean_box(0), x_4, x_17);
lean_dec(x_17);
x_7 = x_19;
x_8 = x_18;
goto block_13;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_71; 
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Term", 4, 4);
x_11 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
lean_inc(x_1);
x_71 = l_Lean_Syntax_isOfKind(x_1, x_12);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_3);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_116; uint8_t x_117; 
x_74 = lean_unsigned_to_nat(0u);
x_102 = lean_unsigned_to_nat(1u);
x_116 = l_Lean_Syntax_getArg(x_1, x_102);
x_117 = l_Lean_Syntax_isNone(x_116);
if (x_117 == 0)
{
uint8_t x_118; 
lean_inc(x_116);
x_118 = l_Lean_Syntax_matchesNull(x_116, x_102);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_116);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_3);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_Syntax_getArg(x_116, x_74);
lean_dec(x_116);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_103 = x_122;
x_104 = x_2;
x_105 = x_3;
goto block_115;
}
}
else
{
lean_object* x_123; 
lean_dec(x_116);
x_123 = lean_box(0);
x_103 = x_123;
x_104 = x_2;
x_105 = x_3;
goto block_115;
}
block_101:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_unsigned_to_nat(5u);
x_80 = l_Lean_Syntax_getArg(x_1, x_79);
x_81 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_82 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_81);
lean_inc(x_80);
x_83 = l_Lean_Syntax_isOfKind(x_80, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_unsigned_to_nat(3u);
x_87 = l_Lean_Syntax_getArg(x_80, x_74);
lean_dec(x_80);
x_88 = l_Lean_Syntax_getArgs(x_87);
lean_dec(x_87);
x_89 = lean_array_get_size(x_88);
x_90 = lean_nat_dec_lt(x_74, x_89);
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_82);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_4 = x_78;
goto block_7;
}
else
{
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_82);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_4 = x_78;
goto block_7;
}
else
{
size_t x_91; size_t x_92; uint8_t x_93; 
x_91 = lean_usize_of_nat(x_74);
x_92 = lean_usize_of_nat(x_89);
x_93 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__0(x_88, x_91, x_92);
if (x_93 == 0)
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_82);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_4 = x_78;
goto block_7;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = l_Lean_Syntax_getArg(x_1, x_86);
lean_dec(x_1);
x_95 = l_Lean_Syntax_getArgs(x_94);
lean_dec(x_94);
x_96 = lean_mk_empty_array_with_capacity(x_74);
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec(x_88);
x_52 = x_75;
x_53 = x_95;
x_54 = x_76;
x_55 = x_82;
x_56 = x_77;
x_57 = x_96;
x_58 = x_78;
goto block_70;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_89, x_89);
lean_dec(x_89);
if (x_97 == 0)
{
lean_dec(x_88);
x_52 = x_75;
x_53 = x_95;
x_54 = x_76;
x_55 = x_82;
x_56 = x_77;
x_57 = x_96;
x_58 = x_78;
goto block_70;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__1(x_88, x_91, x_92, x_96, x_77, x_78);
lean_dec(x_88);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_52 = x_75;
x_53 = x_95;
x_54 = x_76;
x_55 = x_82;
x_56 = x_77;
x_57 = x_99;
x_58 = x_100;
goto block_70;
}
}
}
}
}
}
}
block_115:
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_unsigned_to_nat(2u);
x_107 = l_Lean_Syntax_getArg(x_1, x_106);
x_108 = l_Lean_Syntax_isNone(x_107);
if (x_108 == 0)
{
uint8_t x_109; 
lean_inc(x_107);
x_109 = l_Lean_Syntax_matchesNull(x_107, x_102);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_107);
lean_dec(x_103);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Lean_Syntax_getArg(x_107, x_74);
lean_dec(x_107);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_75 = x_103;
x_76 = x_113;
x_77 = x_104;
x_78 = x_105;
goto block_101;
}
}
else
{
lean_object* x_114; 
lean_dec(x_107);
x_114 = lean_box(0);
x_75 = x_103;
x_76 = x_114;
x_77 = x_104;
x_78 = x_105;
goto block_101;
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_35:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_21);
x_23 = l_Array_append(lean_box(0), x_21, x_22);
lean_dec(x_22);
lean_inc(x_15);
lean_inc(x_18);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_21);
x_25 = l_Array_append(lean_box(0), x_21, x_16);
lean_dec(x_16);
lean_inc(x_15);
lean_inc(x_18);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_18);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Array_append(lean_box(0), x_21, x_13);
lean_dec(x_13);
lean_inc(x_18);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_18);
x_31 = l_Lean_Syntax_node1(x_18, x_19, x_30);
x_32 = l_Lean_Syntax_node6(x_18, x_12, x_14, x_17, x_24, x_26, x_28, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_20);
return x_34;
}
block_51:
{
lean_object* x_46; lean_object* x_47; 
lean_inc(x_44);
x_46 = l_Array_append(lean_box(0), x_44, x_45);
lean_dec(x_45);
lean_inc(x_38);
lean_inc(x_41);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_47, 2, x_46);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_48; 
x_48 = l_Array_empty(lean_box(0));
x_13 = x_36;
x_14 = x_37;
x_15 = x_38;
x_16 = x_40;
x_17 = x_47;
x_18 = x_41;
x_19 = x_42;
x_20 = x_43;
x_21 = x_44;
x_22 = x_48;
goto block_35;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = l_Array_mkArray1___redArg(x_49);
x_13 = x_36;
x_14 = x_37;
x_15 = x_38;
x_16 = x_40;
x_17 = x_47;
x_18 = x_41;
x_19 = x_42;
x_20 = x_43;
x_21 = x_44;
x_22 = x_50;
goto block_35;
}
}
block_70:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_56, 5);
x_60 = lean_box(0);
x_61 = lean_unbox(x_60);
x_62 = l_Lean_SourceInfo_fromRef(x_59, x_61);
lean_inc(x_62);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_11);
x_64 = lean_mk_string_unchecked("null", 4, 4);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_67; 
x_67 = l_Array_empty(lean_box(0));
x_36 = x_57;
x_37 = x_63;
x_38 = x_65;
x_39 = x_54;
x_40 = x_53;
x_41 = x_62;
x_42 = x_55;
x_43 = x_58;
x_44 = x_66;
x_45 = x_67;
goto block_51;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
lean_dec(x_52);
x_69 = l_Array_mkArray1___redArg(x_68);
x_36 = x_57;
x_37 = x_63;
x_38 = x_65;
x_39 = x_54;
x_40 = x_53;
x_41 = x_62;
x_42 = x_55;
x_43 = x_58;
x_44 = x_66;
x_45 = x_69;
goto block_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_expandMatchAlts_x3f_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_expandMatchAlts_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_expandMatchAlts_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_clearInMatchAlt_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Term", 4, 4);
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_SourceInfo_fromRef(x_12, x_14);
x_16 = lean_mk_string_unchecked("clear", 5, 5);
x_17 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_16);
x_18 = lean_mk_string_unchecked("clear%", 6, 6);
lean_inc(x_15);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_uget(x_1, x_3);
x_21 = lean_mk_string_unchecked(";", 1, 1);
lean_inc(x_15);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Syntax_node4(x_15, x_17, x_19, x_20, x_22, x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_4 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_array_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_clearInMatchAlt_spec__0(x_2, x_18, x_20, x_13, x_16, x_17);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_5, x_6, x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_array_fset(x_23, x_6, x_24);
lean_ctor_set(x_1, 2, x_25);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_26 = lean_array_fget(x_5, x_6);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_array_size(x_2);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_usize_of_nat(x_32);
x_34 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_clearInMatchAlt_spec__0(x_2, x_31, x_33, x_26, x_29, x_30);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_5, x_6, x_35);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_array_fset(x_36, x_6, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_38);
return x_39;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_clearInMatchAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_clearInMatchAlt_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatchAlt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_clearInMatchAlt(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_clearInMatch_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Elab_Term_clearInMatchAlt(x_6, x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___redArg(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_49; 
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Parser", 6, 6);
x_8 = lean_mk_string_unchecked("Term", 4, 4);
x_9 = lean_mk_string_unchecked("match", 5, 5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_10 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_9);
lean_inc(x_1);
x_49 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_4);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_93; uint8_t x_94; 
x_51 = lean_unsigned_to_nat(0u);
x_80 = lean_unsigned_to_nat(1u);
x_93 = l_Lean_Syntax_getArg(x_1, x_80);
x_94 = l_Lean_Syntax_isNone(x_93);
if (x_94 == 0)
{
uint8_t x_95; 
lean_inc(x_93);
x_95 = l_Lean_Syntax_matchesNull(x_93, x_80);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_93);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_4);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Lean_Syntax_getArg(x_93, x_51);
lean_dec(x_93);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_81 = x_98;
x_82 = x_3;
x_83 = x_4;
goto block_92;
}
}
else
{
lean_object* x_99; 
lean_dec(x_93);
x_99 = lean_box(0);
x_81 = x_99;
x_82 = x_3;
x_83 = x_4;
goto block_92;
}
block_79:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_unsigned_to_nat(5u);
x_57 = l_Lean_Syntax_getArg(x_1, x_56);
x_58 = lean_mk_string_unchecked("matchAlts", 9, 9);
x_59 = l_Lean_Name_mkStr4(x_6, x_7, x_8, x_58);
lean_inc(x_57);
x_60 = l_Lean_Syntax_isOfKind(x_57, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_10);
lean_dec(x_9);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_unsigned_to_nat(3u);
x_63 = l_Lean_Syntax_getArg(x_1, x_62);
lean_dec(x_1);
x_64 = l_Lean_Syntax_getArg(x_57, x_51);
lean_dec(x_57);
x_65 = l_Lean_Syntax_getArgs(x_64);
lean_dec(x_64);
x_66 = l_Lean_Syntax_getArgs(x_63);
lean_dec(x_63);
x_67 = lean_array_size(x_65);
x_68 = lean_usize_of_nat(x_51);
x_69 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_clearInMatch_spec__0(x_2, x_67, x_68, x_65);
x_70 = lean_ctor_get(x_54, 5);
x_71 = l_Lean_SourceInfo_fromRef(x_70, x_5);
lean_inc(x_71);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_9);
x_73 = lean_mk_string_unchecked("null", 4, 4);
x_74 = l_Lean_Name_mkStr1(x_73);
x_75 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_76; 
x_76 = l_Array_empty(lean_box(0));
x_33 = x_74;
x_34 = x_55;
x_35 = x_75;
x_36 = x_72;
x_37 = x_71;
x_38 = x_53;
x_39 = x_59;
x_40 = x_66;
x_41 = x_69;
x_42 = x_76;
goto block_48;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_52, 0);
lean_inc(x_77);
lean_dec(x_52);
x_78 = l_Array_mkArray1___redArg(x_77);
x_33 = x_74;
x_34 = x_55;
x_35 = x_75;
x_36 = x_72;
x_37 = x_71;
x_38 = x_53;
x_39 = x_59;
x_40 = x_66;
x_41 = x_69;
x_42 = x_78;
goto block_48;
}
}
}
block_92:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_unsigned_to_nat(2u);
x_85 = l_Lean_Syntax_getArg(x_1, x_84);
x_86 = l_Lean_Syntax_isNone(x_85);
if (x_86 == 0)
{
uint8_t x_87; 
lean_inc(x_85);
x_87 = l_Lean_Syntax_matchesNull(x_85, x_80);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_83);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_Syntax_getArg(x_85, x_51);
lean_dec(x_85);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_52 = x_81;
x_53 = x_90;
x_54 = x_82;
x_55 = x_83;
goto block_79;
}
}
else
{
lean_object* x_91; 
lean_dec(x_85);
x_91 = lean_box(0);
x_52 = x_81;
x_53 = x_91;
x_54 = x_82;
x_55 = x_83;
goto block_79;
}
}
}
block_32:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_14);
x_21 = l_Array_append(lean_box(0), x_14, x_20);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_16);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_14);
x_23 = l_Array_append(lean_box(0), x_14, x_18);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_16);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_mk_string_unchecked("with", 4, 4);
lean_inc(x_16);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_append(lean_box(0), x_14, x_19);
lean_dec(x_19);
lean_inc(x_16);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_16);
x_29 = l_Lean_Syntax_node1(x_16, x_17, x_28);
x_30 = l_Lean_Syntax_node6(x_16, x_10, x_15, x_11, x_22, x_24, x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
return x_31;
}
block_48:
{
lean_object* x_43; lean_object* x_44; 
lean_inc(x_35);
x_43 = l_Array_append(lean_box(0), x_35, x_42);
lean_dec(x_42);
lean_inc(x_33);
lean_inc(x_37);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_43);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_45; 
x_45 = l_Array_empty(lean_box(0));
x_11 = x_44;
x_12 = x_33;
x_13 = x_34;
x_14 = x_35;
x_15 = x_36;
x_16 = x_37;
x_17 = x_39;
x_18 = x_40;
x_19 = x_41;
x_20 = x_45;
goto block_32;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = l_Array_mkArray1___redArg(x_46);
x_11 = x_44;
x_12 = x_33;
x_13 = x_34;
x_14 = x_35;
x_15 = x_36;
x_16 = x_37;
x_17 = x_39;
x_18 = x_40;
x_19 = x_41;
x_20 = x_47;
goto block_32;
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_4);
return x_100;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_clearInMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_clearInMatch_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_clearInMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_clearInMatch(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BindersUtil(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
