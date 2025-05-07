// Lean compiler output
// Module: Lake.Util.JsonObject
// Imports: Lean.Data.Json
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
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_instToJson;
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_instCoeJson___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_getJson_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_JsonObject_insert___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_instFromJson;
lean_object* l_Lean_RBNode_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_instCoeJson;
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_JsonObject_mk(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_instCoeJson___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_JsonObject_instCoeJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JsonObject_instCoeJson___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_JsonObject_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JsonObject_toJson), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getObj_x3f(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_JsonObject_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JsonObject_fromJson_x3f), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_JsonObject_insert___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_string_dec_eq(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Lean_RBNode_insert___redArg(x_5, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
x_7 = lean_apply_1(x_2, x_5);
x_8 = l_Lean_RBNode_insert___redArg(x_6, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insert___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_JsonObject_insert___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_Lean_RBNode_insert___redArg(x_6, x_2, x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_insertSome(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
x_8 = lean_apply_1(x_2, x_6);
x_9 = l_Lean_RBNode_insert___redArg(x_7, x_3, x_4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_string_dec_lt(x_1, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_dec_eq(x_1, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_12);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_2);
x_14 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_7);
x_15 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_4, x_5, x_6, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_16 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_box(0);
x_19 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_20);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_2);
x_21 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_4);
x_22 = l_Lean_RBNode_balLeft___redArg(x_21, x_5, x_6, x_7);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_27 = lean_string_dec_lt(x_1, x_24);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_string_dec_eq(x_1, x_24);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_RBNode_isBlack___redArg(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_box(0);
x_31 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_26);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_33);
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_26);
x_35 = l_Lean_RBNode_balRight(lean_box(0), lean_box(0), x_23, x_24, x_25, x_34);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_25);
lean_dec(x_24);
x_36 = l_Lean_RBNode_appendTrees___redArg(x_23, x_26);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = l_Lean_RBNode_isBlack___redArg(x_23);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_box(0);
x_39 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_23);
x_40 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_40, 2, x_25);
lean_ctor_set(x_40, 3, x_26);
x_41 = lean_unbox(x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_41);
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_23);
x_43 = l_Lean_RBNode_balLeft___redArg(x_42, x_24, x_25, x_26);
return x_43;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_2, x_1);
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lake_JsonObject_erase_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_erase___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_JsonObject_erase(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_getJson_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
x_4 = l_Lean_RBNode_find(lean_box(0), x_3, lean_box(0), x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
lean_inc(x_3);
x_5 = l_Lean_RBNode_find(lean_box(0), x_4, lean_box(0), x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = lean_mk_string_unchecked("property not found: ", 20, 20);
x_7 = lean_string_append(x_6, x_3);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_apply_1(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_mk_string_unchecked(": ", 2, 2);
x_14 = lean_string_append(x_3, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_14, x_12);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_mk_string_unchecked(": ", 2, 2);
x_18 = lean_string_append(x_3, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_16);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
lean_inc(x_4);
x_6 = l_Lean_RBNode_find(lean_box(0), x_5, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_mk_string_unchecked("property not found: ", 20, 20);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_1(x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_mk_string_unchecked(": ", 2, 2);
x_15 = lean_string_append(x_4, x_14);
lean_dec(x_14);
x_16 = lean_string_append(x_15, x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_mk_string_unchecked(": ", 2, 2);
x_19 = lean_string_append(x_4, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
lean_dec(x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
lean_inc(x_3);
x_5 = l_Lean_RBNode_find(lean_box(0), x_4, lean_box(0), x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_free_object(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_apply_1(x_1, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_free_object(x_5);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_mk_string_unchecked(": ", 2, 2);
x_16 = lean_string_append(x_3, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_14);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_mk_string_unchecked(": ", 2, 2);
x_20 = lean_string_append(x_3, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_18);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
}
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_apply_1(x_1, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_mk_string_unchecked(": ", 2, 2);
x_34 = lean_string_append(x_3, x_33);
lean_dec(x_33);
x_35 = lean_string_append(x_34, x_31);
lean_dec(x_31);
if (lean_is_scalar(x_32)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_32;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JsonObject_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lake_JsonObject_insert___redArg___lam__0___boxed), 2, 0);
lean_inc(x_4);
x_6 = l_Lean_RBNode_find(lean_box(0), x_5, lean_box(0), x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_apply_1(x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_free_object(x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_mk_string_unchecked(": ", 2, 2);
x_17 = lean_string_append(x_4, x_16);
lean_dec(x_16);
x_18 = lean_string_append(x_17, x_15);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_mk_string_unchecked(": ", 2, 2);
x_21 = lean_string_append(x_4, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_19);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_6, 0, x_25);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
return x_27;
}
}
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_apply_1(x_2, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_mk_string_unchecked(": ", 2, 2);
x_35 = lean_string_append(x_4, x_34);
lean_dec(x_34);
x_36 = lean_string_append(x_35, x_32);
lean_dec(x_32);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_JsonObject(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_JsonObject_instCoeJson = _init_l_Lake_JsonObject_instCoeJson();
lean_mark_persistent(l_Lake_JsonObject_instCoeJson);
l_Lake_JsonObject_instToJson = _init_l_Lake_JsonObject_instToJson();
lean_mark_persistent(l_Lake_JsonObject_instToJson);
l_Lake_JsonObject_instFromJson = _init_l_Lake_JsonObject_instFromJson();
lean_mark_persistent(l_Lake_JsonObject_instFromJson);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
