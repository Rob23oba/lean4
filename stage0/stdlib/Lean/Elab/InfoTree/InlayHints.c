// Lean compiler output
// Module: Lean.Elab.InfoTree.InlayHints
// Imports: Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Syntax_0__String_beqRange____x40_Lean_Syntax___hyg_95_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg(uint8_t, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instTypeNameInlayHint;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_resolveDeferred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_toCustomInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104____boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqInlayHintTextEdit;
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_InlayHintKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_InlayHintKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_InlayHintKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_InlayHintKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_InlayHintKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_InlayHintKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l___private_Lean_Syntax_0__String_beqRange____x40_Lean_Syntax___hyg_95_(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instBEqInlayHintTextEdit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_InlayHints_0__Lean_Elab_beqInlayHintTextEdit____x40_Lean_Elab_InfoTree_InlayHints___hyg_104____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("InlayHint", 9, 9);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instTypeNameInlayHint() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_toCustomInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_;
x_3 = lean_ctor_get(x_1, 1);
x_4 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHint_resolveDeferred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_8);
x_9 = lean_apply_6(x_8, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_InlayHints(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instBEqInlayHintTextEdit = _init_l_Lean_Elab_instBEqInlayHintTextEdit();
lean_mark_persistent(l_Lean_Elab_instBEqInlayHintTextEdit);
l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_ = _init_l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_();
lean_mark_persistent(l_Lean_Elab_instImpl____x40_Lean_Elab_InfoTree_InlayHints___hyg_287_);
l_Lean_Elab_instTypeNameInlayHint = _init_l_Lean_Elab_instTypeNameInlayHint();
lean_mark_persistent(l_Lean_Elab_instTypeNameInlayHint);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
