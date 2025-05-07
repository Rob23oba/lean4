// Lean compiler output
// Module: Lean.Elab.PreDefinition.TerminationHint
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx(uint8_t);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedPartialFixpointType;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTerminationHints;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isGreatest(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isPartial(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_isLeast___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPartialFixpoint;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedDecreasingBy;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isLatticeTheoretic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_none;
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isGreatest___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isPartial___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_elabTerminationHints___redArg___lam__1(uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isLeast(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars_parameters(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTerminationBy;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Expr_getNumHeadLambdas(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t);
static lean_object* _init_l_Lean_Elab_instInhabitedTerminationBy() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty(lean_box(0));
x_4 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*3 + 1, x_6);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDecreasingBy() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_PartialFixpointType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpointType_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_PartialFixpointType_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_PartialFixpointType_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_PartialFixpointType_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpointType_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_PartialFixpointType_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedPartialFixpointType() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialFixpoint() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTerminationHints() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isLeast(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isLeast___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_isLeast(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isGreatest(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isGreatest___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_isGreatest(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isPartial(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isPartial___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_isPartial(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Elab_isLeast(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Elab_isGreatest(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isLatticeTheoretic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_isLatticeTheoretic(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_TerminationHints_none() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
switch (x_26) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_mk_string_unchecked("unused `partial_fixpoint`, function is ", 39, 39);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_stringToMessageData(x_2);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("", 0, 0);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_27, x_34, x_3, x_4, x_5);
return x_35;
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_mk_string_unchecked("unused `greatest_fixpoint`, function is ", 40, 40);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = l_Lean_stringToMessageData(x_2);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_36, x_43, x_3, x_4, x_5);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_mk_string_unchecked("unused `least_fixpoint`, function is ", 37, 37);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = l_Lean_stringToMessageData(x_2);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("", 0, 0);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_45, x_52, x_3, x_4, x_5);
return x_53;
}
}
}
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_21, 0);
x_56 = lean_ctor_get(x_55, 0);
x_57 = lean_mk_string_unchecked("unused `decreasing_by`, function is ", 36, 36);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = l_Lean_stringToMessageData(x_2);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_mk_string_unchecked("", 0, 0);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_56, x_63, x_3, x_4, x_5);
return x_64;
}
else
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_5;
goto block_18;
}
}
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_20, 0);
x_68 = lean_ctor_get(x_67, 0);
x_69 = lean_mk_string_unchecked("unused `termination_by`, function is ", 37, 37);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = l_Lean_stringToMessageData(x_2);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_68, x_75, x_3, x_4, x_5);
return x_76;
}
else
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_5;
goto block_18;
}
}
else
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_5;
goto block_18;
}
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_19, 0);
x_81 = lean_mk_string_unchecked("unused `termination_by\?`, function is ", 38, 38);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = l_Lean_stringToMessageData(x_2);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked("", 0, 0);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_80, x_87, x_3, x_4, x_5);
return x_88;
}
else
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_5;
goto block_18;
}
}
else
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_5;
goto block_18;
}
}
else
{
x_6 = x_3;
x_7 = x_4;
x_8 = x_5;
goto block_18;
}
}
block_18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_mk_string_unchecked("unused termination hints, function is ", 38, 38);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = l_Lean_stringToMessageData(x_2);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_9, x_16, x_6, x_7, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___Lean_Elab_TerminationHints_ensureNone_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_ensureNone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_TerminationHints_ensureNone(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_TerminationHints_isNotNone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_isNotNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_TerminationHints_isNotNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
x_9 = l_Lean_Expr_getNumHeadLambdas(x_3);
x_10 = lean_nat_sub(x_9, x_1);
lean_dec(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set(x_11, 5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_TerminationHints_rememberExtraParams(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars_parameters(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_mk_string_unchecked("", 0, 0);
x_5 = l_Lean_stringToMessageData(x_4);
lean_dec(x_4);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked(" parameters", 11, 11);
x_11 = l_Lean_stringToMessageData(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("one parameter", 13, 13);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_replaceRef(x_1, x_8);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
x_14 = lean_ctor_get(x_5, 4);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_5, 8);
x_18 = lean_ctor_get(x_5, 9);
x_19 = lean_ctor_get(x_5, 10);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_21 = lean_ctor_get(x_5, 11);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_23 = lean_ctor_get(x_5, 12);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_24 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_24, 3, x_13);
lean_ctor_set(x_24, 4, x_14);
lean_ctor_set(x_24, 5, x_9);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set(x_24, 7, x_16);
lean_ctor_set(x_24, 8, x_17);
lean_ctor_set(x_24, 9, x_18);
lean_ctor_set(x_24, 10, x_19);
lean_ctor_set(x_24, 11, x_21);
lean_ctor_set(x_24, 12, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*13, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*13 + 1, x_22);
x_25 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_2, x_3, x_4, x_24, x_6, x_7);
lean_dec(x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_array_get_size(x_19);
x_21 = lean_nat_dec_lt(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_24 = lean_mk_string_unchecked("", 0, 0);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = l_Lean_Elab_TerminationBy_checkVars_parameters(x_20);
lean_inc(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked(" bound in `termination_by`, but the body of ", 44, 44);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_1);
x_31 = l_Lean_MessageData_ofName(x_1);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked(" only binds ", 12, 12);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_TerminationBy_checkVars_parameters(x_2);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked(".", 1, 1);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_fget(x_19, x_42);
x_44 = lean_mk_string_unchecked("ident", 5, 5);
x_45 = l_Lean_Name_mkStr1(x_44);
lean_inc(x_43);
x_46 = l_Lean_Syntax_isOfKind(x_43, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_dec(x_43);
lean_dec(x_1);
x_9 = x_41;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_17;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Syntax_getId(x_43);
lean_dec(x_43);
x_48 = l_Lean_Name_isSuffixOf(x_47, x_1);
lean_dec(x_1);
lean_dec(x_47);
if (x_48 == 0)
{
x_9 = x_41;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_17;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_mk_string_unchecked(" (Since Lean v4.6.0, the `termination_by` clause no longer ", 59, 59);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_mk_string_unchecked("expects the function name here.)", 32, 32);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_9 = x_55;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_17;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
return x_57;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___redArg(x_15, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___Lean_Elab_TerminationBy_checkVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_TerminationBy_checkVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_TerminationBy_checkVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabTerminationHints___redArg___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
x_8 = x_12;
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
x_8 = x_6;
goto block_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_8 = x_15;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_4);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_4);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__2), 7, 6);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_4, lean_box(0), x_18);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_28 = lean_mk_string_unchecked("decreasingBy", 12, 12);
x_29 = l_Lean_Name_mkStr4(x_10, x_11, x_12, x_28);
lean_inc(x_21);
x_30 = l_Lean_Syntax_isOfKind(x_21, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_31 = lean_mk_string_unchecked("unexpected `decreasing_by` syntax", 33, 33);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_13, x_14, x_21, x_32);
x_24 = x_33;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_14);
lean_dec(x_13);
x_34 = l_Lean_Syntax_getArg(x_21, x_15);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_apply_2(x_4, lean_box(0), x_35);
x_24 = x_36;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_apply_4(x_23, lean_box(0), lean_box(0), x_9, x_24);
x_26 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_25, x_17);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__3___boxed), 16, 15);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_7);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
lean_closure_set(x_17, 10, x_10);
lean_closure_set(x_17, 11, x_11);
lean_closure_set(x_17, 12, x_12);
lean_closure_set(x_17, 13, x_13);
lean_closure_set(x_17, 14, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_3, lean_box(0), x_19);
x_21 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_23 = x_15;
} else {
 lean_dec_ref(x_15);
 x_23 = lean_box(0);
}
x_24 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_24);
lean_inc(x_22);
x_26 = l_Lean_Syntax_isOfKind(x_22, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_mk_string_unchecked("greatestFixpoint", 16, 16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_27);
lean_inc(x_22);
x_29 = l_Lean_Syntax_isOfKind(x_22, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_mk_string_unchecked("leastFixpoint", 13, 13);
x_31 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_30);
lean_inc(x_22);
x_32 = l_Lean_Syntax_isOfKind(x_22, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(x_33, 0, x_17);
x_34 = lean_box(0);
x_35 = lean_apply_2(x_3, lean_box(0), x_34);
x_36 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_35, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_46; uint8_t x_47; 
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(x_37, 0, x_17);
x_46 = l_Lean_Syntax_getArg(x_22, x_14);
x_47 = l_Lean_Syntax_isNone(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_unsigned_to_nat(2u);
lean_inc(x_46);
x_49 = l_Lean_Syntax_matchesNull(x_46, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_46);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
x_50 = lean_box(0);
x_51 = lean_apply_2(x_3, lean_box(0), x_50);
x_52 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_51, x_37);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_Syntax_getArg(x_46, x_14);
lean_dec(x_14);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_38 = x_54;
goto block_45;
}
}
else
{
lean_object* x_55; 
lean_dec(x_46);
lean_dec(x_14);
x_55 = lean_box(0);
x_38 = x_55;
goto block_45;
}
block_45:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_23)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_23;
}
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_apply_2(x_3, lean_box(0), x_42);
x_44 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_43, x_37);
return x_44;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_65; uint8_t x_66; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(x_56, 0, x_17);
x_65 = l_Lean_Syntax_getArg(x_22, x_14);
x_66 = l_Lean_Syntax_isNone(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_unsigned_to_nat(2u);
lean_inc(x_65);
x_68 = l_Lean_Syntax_matchesNull(x_65, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
x_69 = lean_box(0);
x_70 = lean_apply_2(x_3, lean_box(0), x_69);
x_71 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_70, x_56);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Syntax_getArg(x_65, x_14);
lean_dec(x_14);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_57 = x_73;
goto block_64;
}
}
else
{
lean_object* x_74; 
lean_dec(x_65);
lean_dec(x_14);
x_74 = lean_box(0);
x_57 = x_74;
goto block_64;
}
block_64:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_22);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_60);
if (lean_is_scalar(x_23)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_23;
}
lean_ctor_set(x_61, 0, x_59);
x_62 = lean_apply_2(x_3, lean_box(0), x_61);
x_63 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_62, x_56);
return x_63;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_84; uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_75 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__4), 2, 1);
lean_closure_set(x_75, 0, x_17);
x_84 = l_Lean_Syntax_getArg(x_22, x_14);
x_85 = l_Lean_Syntax_isNone(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_unsigned_to_nat(2u);
lean_inc(x_84);
x_87 = l_Lean_Syntax_matchesNull(x_84, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_84);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
x_88 = lean_box(0);
x_89 = lean_apply_2(x_3, lean_box(0), x_88);
x_90 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_89, x_75);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Lean_Syntax_getArg(x_84, x_14);
lean_dec(x_14);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_76 = x_92;
goto block_83;
}
}
else
{
lean_object* x_93; 
lean_dec(x_84);
lean_dec(x_14);
x_93 = lean_box(0);
x_76 = x_93;
goto block_83;
}
block_83:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_78, 0, x_22);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_79);
if (lean_is_scalar(x_23)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_23;
}
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_apply_2(x_3, lean_box(0), x_80);
x_82 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_81, x_75);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_1, x_2, x_3, x_8);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked("no extra parameters bounds, please omit the `=>`", 48, 48);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_1, x_2, x_3, x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_9 = x_19;
goto block_17;
}
else
{
x_9 = x_6;
goto block_17;
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_mk_empty_array_with_capacity(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_9);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3 + 1, x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_apply_2(x_3, lean_box(0), x_14);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_9 = x_18;
goto block_16;
}
else
{
x_9 = x_5;
goto block_16;
}
block_16:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_apply_2(x_2, lean_box(0), x_13);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__12), 16, 15);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_6);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
lean_closure_set(x_16, 9, x_9);
lean_closure_set(x_16, 10, x_10);
lean_closure_set(x_16, 11, x_11);
lean_closure_set(x_16, 12, x_12);
lean_closure_set(x_16, 13, x_13);
lean_closure_set(x_16, 14, x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_3, lean_box(0), x_18);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_mk_string_unchecked("terminationBy", 13, 13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_23);
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_14);
lean_dec(x_2);
x_26 = lean_mk_string_unchecked("terminationBy\?", 14, 14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_26);
lean_inc(x_22);
x_28 = l_Lean_Syntax_isOfKind(x_22, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_29);
lean_inc(x_22);
x_31 = l_Lean_Syntax_isOfKind(x_22, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_mk_string_unchecked("greatestFixpoint", 16, 16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_32);
lean_inc(x_22);
x_34 = l_Lean_Syntax_isOfKind(x_22, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_mk_string_unchecked("leastFixpoint", 13, 13);
x_36 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_35);
lean_inc(x_22);
x_37 = l_Lean_Syntax_isOfKind(x_22, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_13);
lean_dec(x_3);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_38, 0, x_16);
x_39 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_22, x_40);
x_42 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_41, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_48; uint8_t x_49; 
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_43, 0, x_16);
x_48 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_13);
x_49 = l_Lean_Syntax_isNone(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Syntax_matchesNull(x_48, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
x_52 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_22, x_53);
x_55 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_54, x_43);
return x_55;
}
else
{
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
goto block_47;
}
}
else
{
lean_dec(x_48);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
goto block_47;
}
block_47:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_box(0);
x_45 = lean_apply_2(x_3, lean_box(0), x_44);
x_46 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_45, x_43);
return x_46;
}
}
}
else
{
lean_object* x_56; lean_object* x_61; uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_56, 0, x_16);
x_61 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_13);
x_62 = l_Lean_Syntax_isNone(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_unsigned_to_nat(2u);
x_64 = l_Lean_Syntax_matchesNull(x_61, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
x_65 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_22, x_66);
x_68 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_67, x_56);
return x_68;
}
else
{
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
goto block_60;
}
}
else
{
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
goto block_60;
}
block_60:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_box(0);
x_58 = lean_apply_2(x_3, lean_box(0), x_57);
x_59 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_58, x_56);
return x_59;
}
}
}
else
{
lean_object* x_69; lean_object* x_74; uint8_t x_75; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_69 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_69, 0, x_16);
x_74 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_13);
x_75 = l_Lean_Syntax_isNone(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_unsigned_to_nat(2u);
x_77 = l_Lean_Syntax_matchesNull(x_74, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
x_78 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
x_80 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_22, x_79);
x_81 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_80, x_69);
return x_81;
}
else
{
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
goto block_73;
}
}
else
{
lean_dec(x_74);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_11);
goto block_73;
}
block_73:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_box(0);
x_71 = lean_apply_2(x_3, lean_box(0), x_70);
x_72 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_71, x_69);
return x_72;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_82 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_82, 0, x_16);
x_83 = lean_box(0);
x_84 = lean_apply_2(x_3, lean_box(0), x_83);
x_85 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_84, x_82);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_107; uint8_t x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_86 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_86, 0, x_16);
x_107 = l_Lean_Syntax_getArg(x_22, x_13);
lean_inc(x_107);
x_108 = l_Lean_Syntax_matchesNull(x_107, x_2);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = l_Lean_Syntax_isNone(x_107);
if (x_109 == 0)
{
uint8_t x_110; 
lean_inc(x_107);
x_110 = l_Lean_Syntax_matchesNull(x_107, x_13);
lean_dec(x_13);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
lean_free_object(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_111 = lean_box(0);
x_112 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_22, x_5, x_86, x_111);
return x_112;
}
else
{
lean_object* x_113; 
x_113 = l_Lean_Syntax_getArg(x_107, x_2);
lean_dec(x_107);
lean_ctor_set(x_14, 0, x_113);
x_87 = x_14;
goto block_106;
}
}
else
{
lean_object* x_114; 
lean_dec(x_107);
lean_free_object(x_14);
lean_dec(x_13);
x_114 = lean_box(0);
x_87 = x_114;
goto block_106;
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_unsigned_to_nat(2u);
x_116 = l_Lean_Syntax_getArg(x_22, x_115);
lean_inc(x_116);
x_117 = l_Lean_Syntax_matchesNull(x_116, x_2);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_133; 
x_118 = lean_unsigned_to_nat(3u);
x_133 = l_Lean_Syntax_isNone(x_107);
if (x_133 == 0)
{
uint8_t x_134; 
lean_inc(x_107);
x_134 = l_Lean_Syntax_matchesNull(x_107, x_13);
lean_dec(x_13);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_116);
lean_dec(x_107);
lean_free_object(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_box(0);
x_136 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_22, x_5, x_86, x_135);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = l_Lean_Syntax_getArg(x_107, x_2);
lean_dec(x_107);
lean_ctor_set(x_14, 0, x_137);
x_119 = x_14;
goto block_132;
}
}
else
{
lean_object* x_138; 
lean_dec(x_107);
lean_free_object(x_14);
lean_dec(x_13);
x_138 = lean_box(0);
x_119 = x_138;
goto block_132;
}
block_132:
{
uint8_t x_120; 
lean_inc(x_116);
x_120 = l_Lean_Syntax_matchesNull(x_116, x_115);
if (x_120 == 0)
{
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_119);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_box(0);
x_122 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_22, x_5, x_86, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_12);
lean_dec(x_11);
x_123 = l_Lean_Syntax_getArg(x_22, x_118);
x_124 = l_Lean_Elab_elabTerminationHints___redArg___lam__7(x_2, x_22, x_3, x_5, x_86, x_25, x_119, x_123);
lean_dec(x_119);
lean_dec(x_2);
return x_124;
}
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = l_Lean_Syntax_getArg(x_116, x_2);
lean_dec(x_116);
lean_inc(x_125);
x_126 = l_Lean_Syntax_matchesNull(x_125, x_2);
lean_dec(x_2);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_12);
lean_dec(x_11);
x_127 = l_Lean_Syntax_getArg(x_22, x_118);
x_128 = l_Lean_Syntax_getArgs(x_125);
lean_dec(x_125);
x_129 = l_Lean_Elab_elabTerminationHints___redArg___lam__8(x_22, x_3, x_5, x_86, x_25, x_119, x_128, x_127);
lean_dec(x_119);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
lean_dec(x_3);
x_130 = l_Lean_Syntax_getArg(x_22, x_118);
x_131 = l_Lean_Elab_elabTerminationHints___redArg___lam__6(x_11, x_12, x_22, x_5, x_86, x_119, x_130);
lean_dec(x_130);
lean_dec(x_119);
return x_131;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_139 = lean_unsigned_to_nat(3u);
x_154 = l_Lean_Syntax_getArg(x_22, x_139);
x_155 = lean_mk_string_unchecked("partialFixpointursion", 21, 21);
x_156 = l_Lean_Name_mkStr1(x_155);
x_157 = l_Lean_Syntax_matchesIdent(x_154, x_156);
lean_dec(x_154);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Syntax_isNone(x_107);
if (x_158 == 0)
{
uint8_t x_159; 
lean_inc(x_107);
x_159 = l_Lean_Syntax_matchesNull(x_107, x_13);
lean_dec(x_13);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_116);
lean_dec(x_107);
lean_free_object(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_160 = lean_box(0);
x_161 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_22, x_5, x_86, x_160);
return x_161;
}
else
{
lean_object* x_162; 
x_162 = l_Lean_Syntax_getArg(x_107, x_2);
lean_dec(x_107);
lean_ctor_set(x_14, 0, x_162);
x_140 = x_14;
goto block_153;
}
}
else
{
lean_object* x_163; 
lean_dec(x_107);
lean_free_object(x_14);
lean_dec(x_13);
x_163 = lean_box(0);
x_140 = x_163;
goto block_153;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_116);
lean_dec(x_107);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_164 = lean_box(0);
x_165 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_167, 0, x_22);
lean_ctor_set(x_167, 1, x_165);
lean_ctor_set(x_167, 2, x_166);
x_168 = lean_unbox(x_164);
lean_ctor_set_uint8(x_167, sizeof(void*)*3, x_168);
x_169 = lean_unbox(x_164);
lean_ctor_set_uint8(x_167, sizeof(void*)*3 + 1, x_169);
lean_ctor_set(x_14, 0, x_167);
x_170 = lean_apply_2(x_3, lean_box(0), x_14);
x_171 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_170, x_86);
return x_171;
}
block_153:
{
uint8_t x_141; 
lean_inc(x_116);
x_141 = l_Lean_Syntax_matchesNull(x_116, x_115);
if (x_141 == 0)
{
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_140);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_box(0);
x_143 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_22, x_5, x_86, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_12);
lean_dec(x_11);
x_144 = l_Lean_Syntax_getArg(x_22, x_139);
x_145 = l_Lean_Elab_elabTerminationHints___redArg___lam__7(x_2, x_22, x_3, x_5, x_86, x_25, x_140, x_144);
lean_dec(x_140);
lean_dec(x_2);
return x_145;
}
}
else
{
lean_object* x_146; uint8_t x_147; 
x_146 = l_Lean_Syntax_getArg(x_116, x_2);
lean_dec(x_116);
lean_inc(x_146);
x_147 = l_Lean_Syntax_matchesNull(x_146, x_2);
lean_dec(x_2);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_12);
lean_dec(x_11);
x_148 = l_Lean_Syntax_getArg(x_22, x_139);
x_149 = l_Lean_Syntax_getArgs(x_146);
lean_dec(x_146);
x_150 = l_Lean_Elab_elabTerminationHints___redArg___lam__8(x_22, x_3, x_5, x_86, x_25, x_140, x_149, x_148);
lean_dec(x_140);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_146);
lean_dec(x_3);
x_151 = l_Lean_Syntax_getArg(x_22, x_139);
x_152 = l_Lean_Elab_elabTerminationHints___redArg___lam__6(x_11, x_12, x_22, x_5, x_86, x_140, x_151);
lean_dec(x_151);
lean_dec(x_140);
return x_152;
}
}
}
}
}
block_106:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_unsigned_to_nat(2u);
x_89 = l_Lean_Syntax_getArg(x_22, x_88);
lean_inc(x_89);
x_90 = l_Lean_Syntax_matchesNull(x_89, x_88);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Syntax_matchesNull(x_89, x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(0);
x_93 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_22, x_5, x_86, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_12);
lean_dec(x_11);
x_94 = lean_unsigned_to_nat(3u);
x_95 = l_Lean_Syntax_getArg(x_22, x_94);
x_96 = l_Lean_Elab_elabTerminationHints___redArg___lam__7(x_2, x_22, x_3, x_5, x_86, x_25, x_87, x_95);
lean_dec(x_87);
lean_dec(x_2);
return x_96;
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = l_Lean_Syntax_getArg(x_89, x_2);
lean_dec(x_89);
lean_inc(x_97);
x_98 = l_Lean_Syntax_matchesNull(x_97, x_2);
lean_dec(x_2);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_12);
lean_dec(x_11);
x_99 = lean_unsigned_to_nat(3u);
x_100 = l_Lean_Syntax_getArg(x_22, x_99);
x_101 = l_Lean_Syntax_getArgs(x_97);
lean_dec(x_97);
x_102 = l_Lean_Elab_elabTerminationHints___redArg___lam__8(x_22, x_3, x_5, x_86, x_25, x_87, x_101, x_100);
lean_dec(x_87);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_97);
lean_dec(x_3);
x_103 = lean_unsigned_to_nat(3u);
x_104 = l_Lean_Syntax_getArg(x_22, x_103);
x_105 = l_Lean_Elab_elabTerminationHints___redArg___lam__6(x_11, x_12, x_22, x_5, x_86, x_87, x_104);
lean_dec(x_104);
lean_dec(x_87);
return x_105;
}
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_172 = lean_ctor_get(x_14, 0);
lean_inc(x_172);
lean_dec(x_14);
x_173 = lean_mk_string_unchecked("terminationBy", 13, 13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_174 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_173);
lean_inc(x_172);
x_175 = l_Lean_Syntax_isOfKind(x_172, x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_dec(x_2);
x_176 = lean_mk_string_unchecked("terminationBy\?", 14, 14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_177 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_176);
lean_inc(x_172);
x_178 = l_Lean_Syntax_isOfKind(x_172, x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_180 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_179);
lean_inc(x_172);
x_181 = l_Lean_Syntax_isOfKind(x_172, x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_mk_string_unchecked("greatestFixpoint", 16, 16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_183 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_182);
lean_inc(x_172);
x_184 = l_Lean_Syntax_isOfKind(x_172, x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_mk_string_unchecked("leastFixpoint", 13, 13);
x_186 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_185);
lean_inc(x_172);
x_187 = l_Lean_Syntax_isOfKind(x_172, x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_13);
lean_dec(x_3);
x_188 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_188, 0, x_16);
x_189 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_190 = l_Lean_stringToMessageData(x_189);
lean_dec(x_189);
x_191 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_172, x_190);
x_192 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_191, x_188);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_198; uint8_t x_199; 
x_193 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_193, 0, x_16);
x_198 = l_Lean_Syntax_getArg(x_172, x_13);
lean_dec(x_13);
x_199 = l_Lean_Syntax_isNone(x_198);
if (x_199 == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_unsigned_to_nat(2u);
x_201 = l_Lean_Syntax_matchesNull(x_198, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_3);
x_202 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_203 = l_Lean_stringToMessageData(x_202);
lean_dec(x_202);
x_204 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_172, x_203);
x_205 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_204, x_193);
return x_205;
}
else
{
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
goto block_197;
}
}
else
{
lean_dec(x_198);
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
goto block_197;
}
block_197:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_box(0);
x_195 = lean_apply_2(x_3, lean_box(0), x_194);
x_196 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_195, x_193);
return x_196;
}
}
}
else
{
lean_object* x_206; lean_object* x_211; uint8_t x_212; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_206 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_206, 0, x_16);
x_211 = l_Lean_Syntax_getArg(x_172, x_13);
lean_dec(x_13);
x_212 = l_Lean_Syntax_isNone(x_211);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_unsigned_to_nat(2u);
x_214 = l_Lean_Syntax_matchesNull(x_211, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_3);
x_215 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_216 = l_Lean_stringToMessageData(x_215);
lean_dec(x_215);
x_217 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_172, x_216);
x_218 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_217, x_206);
return x_218;
}
else
{
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
goto block_210;
}
}
else
{
lean_dec(x_211);
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
goto block_210;
}
block_210:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_box(0);
x_208 = lean_apply_2(x_3, lean_box(0), x_207);
x_209 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_208, x_206);
return x_209;
}
}
}
else
{
lean_object* x_219; lean_object* x_224; uint8_t x_225; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_219 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_219, 0, x_16);
x_224 = l_Lean_Syntax_getArg(x_172, x_13);
lean_dec(x_13);
x_225 = l_Lean_Syntax_isNone(x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_unsigned_to_nat(2u);
x_227 = l_Lean_Syntax_matchesNull(x_224, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_3);
x_228 = lean_mk_string_unchecked("unexpected `termination_by` syntax", 34, 34);
x_229 = l_Lean_stringToMessageData(x_228);
lean_dec(x_228);
x_230 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_11, x_12, x_172, x_229);
x_231 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_230, x_219);
return x_231;
}
else
{
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
goto block_223;
}
}
else
{
lean_dec(x_224);
lean_dec(x_172);
lean_dec(x_12);
lean_dec(x_11);
goto block_223;
}
block_223:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_box(0);
x_221 = lean_apply_2(x_3, lean_box(0), x_220);
x_222 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_221, x_219);
return x_222;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_172);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_232 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_232, 0, x_16);
x_233 = lean_box(0);
x_234 = lean_apply_2(x_3, lean_box(0), x_233);
x_235 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_234, x_232);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_257; uint8_t x_258; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_236 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__5), 2, 1);
lean_closure_set(x_236, 0, x_16);
x_257 = l_Lean_Syntax_getArg(x_172, x_13);
lean_inc(x_257);
x_258 = l_Lean_Syntax_matchesNull(x_257, x_2);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = l_Lean_Syntax_isNone(x_257);
if (x_259 == 0)
{
uint8_t x_260; 
lean_inc(x_257);
x_260 = l_Lean_Syntax_matchesNull(x_257, x_13);
lean_dec(x_13);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_257);
lean_dec(x_3);
lean_dec(x_2);
x_261 = lean_box(0);
x_262 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_172, x_5, x_236, x_261);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = l_Lean_Syntax_getArg(x_257, x_2);
lean_dec(x_257);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_237 = x_264;
goto block_256;
}
}
else
{
lean_object* x_265; 
lean_dec(x_257);
lean_dec(x_13);
x_265 = lean_box(0);
x_237 = x_265;
goto block_256;
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_266 = lean_unsigned_to_nat(2u);
x_267 = l_Lean_Syntax_getArg(x_172, x_266);
lean_inc(x_267);
x_268 = l_Lean_Syntax_matchesNull(x_267, x_2);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; uint8_t x_284; 
x_269 = lean_unsigned_to_nat(3u);
x_284 = l_Lean_Syntax_isNone(x_257);
if (x_284 == 0)
{
uint8_t x_285; 
lean_inc(x_257);
x_285 = l_Lean_Syntax_matchesNull(x_257, x_13);
lean_dec(x_13);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_267);
lean_dec(x_257);
lean_dec(x_3);
lean_dec(x_2);
x_286 = lean_box(0);
x_287 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_172, x_5, x_236, x_286);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = l_Lean_Syntax_getArg(x_257, x_2);
lean_dec(x_257);
x_289 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_270 = x_289;
goto block_283;
}
}
else
{
lean_object* x_290; 
lean_dec(x_257);
lean_dec(x_13);
x_290 = lean_box(0);
x_270 = x_290;
goto block_283;
}
block_283:
{
uint8_t x_271; 
lean_inc(x_267);
x_271 = l_Lean_Syntax_matchesNull(x_267, x_266);
if (x_271 == 0)
{
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_270);
lean_dec(x_3);
lean_dec(x_2);
x_272 = lean_box(0);
x_273 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_172, x_5, x_236, x_272);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_12);
lean_dec(x_11);
x_274 = l_Lean_Syntax_getArg(x_172, x_269);
x_275 = l_Lean_Elab_elabTerminationHints___redArg___lam__7(x_2, x_172, x_3, x_5, x_236, x_175, x_270, x_274);
lean_dec(x_270);
lean_dec(x_2);
return x_275;
}
}
else
{
lean_object* x_276; uint8_t x_277; 
x_276 = l_Lean_Syntax_getArg(x_267, x_2);
lean_dec(x_267);
lean_inc(x_276);
x_277 = l_Lean_Syntax_matchesNull(x_276, x_2);
lean_dec(x_2);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_12);
lean_dec(x_11);
x_278 = l_Lean_Syntax_getArg(x_172, x_269);
x_279 = l_Lean_Syntax_getArgs(x_276);
lean_dec(x_276);
x_280 = l_Lean_Elab_elabTerminationHints___redArg___lam__8(x_172, x_3, x_5, x_236, x_175, x_270, x_279, x_278);
lean_dec(x_270);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_276);
lean_dec(x_3);
x_281 = l_Lean_Syntax_getArg(x_172, x_269);
x_282 = l_Lean_Elab_elabTerminationHints___redArg___lam__6(x_11, x_12, x_172, x_5, x_236, x_270, x_281);
lean_dec(x_281);
lean_dec(x_270);
return x_282;
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_291 = lean_unsigned_to_nat(3u);
x_306 = l_Lean_Syntax_getArg(x_172, x_291);
x_307 = lean_mk_string_unchecked("partialFixpointursion", 21, 21);
x_308 = l_Lean_Name_mkStr1(x_307);
x_309 = l_Lean_Syntax_matchesIdent(x_306, x_308);
lean_dec(x_306);
if (x_309 == 0)
{
uint8_t x_310; 
x_310 = l_Lean_Syntax_isNone(x_257);
if (x_310 == 0)
{
uint8_t x_311; 
lean_inc(x_257);
x_311 = l_Lean_Syntax_matchesNull(x_257, x_13);
lean_dec(x_13);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_267);
lean_dec(x_257);
lean_dec(x_3);
lean_dec(x_2);
x_312 = lean_box(0);
x_313 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_172, x_5, x_236, x_312);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = l_Lean_Syntax_getArg(x_257, x_2);
lean_dec(x_257);
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_314);
x_292 = x_315;
goto block_305;
}
}
else
{
lean_object* x_316; 
lean_dec(x_257);
lean_dec(x_13);
x_316 = lean_box(0);
x_292 = x_316;
goto block_305;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_267);
lean_dec(x_257);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_317 = lean_box(0);
x_318 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_319 = lean_box(0);
x_320 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_320, 0, x_172);
lean_ctor_set(x_320, 1, x_318);
lean_ctor_set(x_320, 2, x_319);
x_321 = lean_unbox(x_317);
lean_ctor_set_uint8(x_320, sizeof(void*)*3, x_321);
x_322 = lean_unbox(x_317);
lean_ctor_set_uint8(x_320, sizeof(void*)*3 + 1, x_322);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_320);
x_324 = lean_apply_2(x_3, lean_box(0), x_323);
x_325 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_324, x_236);
return x_325;
}
block_305:
{
uint8_t x_293; 
lean_inc(x_267);
x_293 = l_Lean_Syntax_matchesNull(x_267, x_266);
if (x_293 == 0)
{
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_292);
lean_dec(x_3);
lean_dec(x_2);
x_294 = lean_box(0);
x_295 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_172, x_5, x_236, x_294);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_12);
lean_dec(x_11);
x_296 = l_Lean_Syntax_getArg(x_172, x_291);
x_297 = l_Lean_Elab_elabTerminationHints___redArg___lam__7(x_2, x_172, x_3, x_5, x_236, x_175, x_292, x_296);
lean_dec(x_292);
lean_dec(x_2);
return x_297;
}
}
else
{
lean_object* x_298; uint8_t x_299; 
x_298 = l_Lean_Syntax_getArg(x_267, x_2);
lean_dec(x_267);
lean_inc(x_298);
x_299 = l_Lean_Syntax_matchesNull(x_298, x_2);
lean_dec(x_2);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_12);
lean_dec(x_11);
x_300 = l_Lean_Syntax_getArg(x_172, x_291);
x_301 = l_Lean_Syntax_getArgs(x_298);
lean_dec(x_298);
x_302 = l_Lean_Elab_elabTerminationHints___redArg___lam__8(x_172, x_3, x_5, x_236, x_175, x_292, x_301, x_300);
lean_dec(x_292);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_298);
lean_dec(x_3);
x_303 = l_Lean_Syntax_getArg(x_172, x_291);
x_304 = l_Lean_Elab_elabTerminationHints___redArg___lam__6(x_11, x_12, x_172, x_5, x_236, x_292, x_303);
lean_dec(x_303);
lean_dec(x_292);
return x_304;
}
}
}
}
}
block_256:
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_unsigned_to_nat(2u);
x_239 = l_Lean_Syntax_getArg(x_172, x_238);
lean_inc(x_239);
x_240 = l_Lean_Syntax_matchesNull(x_239, x_238);
if (x_240 == 0)
{
uint8_t x_241; 
x_241 = l_Lean_Syntax_matchesNull(x_239, x_2);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_237);
lean_dec(x_3);
lean_dec(x_2);
x_242 = lean_box(0);
x_243 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_11, x_12, x_172, x_5, x_236, x_242);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_12);
lean_dec(x_11);
x_244 = lean_unsigned_to_nat(3u);
x_245 = l_Lean_Syntax_getArg(x_172, x_244);
x_246 = l_Lean_Elab_elabTerminationHints___redArg___lam__7(x_2, x_172, x_3, x_5, x_236, x_175, x_237, x_245);
lean_dec(x_237);
lean_dec(x_2);
return x_246;
}
}
else
{
lean_object* x_247; uint8_t x_248; 
x_247 = l_Lean_Syntax_getArg(x_239, x_2);
lean_dec(x_239);
lean_inc(x_247);
x_248 = l_Lean_Syntax_matchesNull(x_247, x_2);
lean_dec(x_2);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_12);
lean_dec(x_11);
x_249 = lean_unsigned_to_nat(3u);
x_250 = l_Lean_Syntax_getArg(x_172, x_249);
x_251 = l_Lean_Syntax_getArgs(x_247);
lean_dec(x_247);
x_252 = l_Lean_Elab_elabTerminationHints___redArg___lam__8(x_172, x_3, x_5, x_236, x_175, x_237, x_251, x_250);
lean_dec(x_237);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_247);
lean_dec(x_3);
x_253 = lean_unsigned_to_nat(3u);
x_254 = l_Lean_Syntax_getArg(x_172, x_253);
x_255 = l_Lean_Elab_elabTerminationHints___redArg___lam__6(x_11, x_12, x_172, x_5, x_236, x_237, x_254);
lean_dec(x_254);
lean_dec(x_237);
return x_255;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Termination", 11, 11);
x_12 = lean_mk_string_unchecked("suffix", 6, 6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("Unexpected Termination.suffix syntax: ", 38, 38);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = l_Lean_Syntax_formatStx(x_1, x_18, x_14);
x_20 = lean_unsigned_to_nat(120u);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_format_pretty(x_19, x_20, x_21, x_21);
x_23 = lean_string_append(x_17, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked(" of kind ", 9, 9);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
lean_inc(x_1);
x_26 = l_Lean_Syntax_getKind(x_1);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
x_29 = l_Lean_Name_toString(x_26, x_28, x_16);
x_30 = lean_string_append(x_25, x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_2, x_3, x_1, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_54; lean_object* x_98; uint8_t x_99; 
x_34 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_Syntax_getArg(x_1, x_34);
x_99 = l_Lean_Syntax_isNone(x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_unsigned_to_nat(1u);
lean_inc(x_98);
x_101 = l_Lean_Syntax_matchesNull(x_98, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = lean_box(x_101);
x_103 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_103, 0, x_102);
x_104 = lean_mk_string_unchecked("Unexpected Termination.suffix syntax: ", 38, 38);
x_105 = lean_box(0);
lean_inc(x_1);
x_106 = l_Lean_Syntax_formatStx(x_1, x_105, x_101);
x_107 = lean_unsigned_to_nat(120u);
x_108 = lean_format_pretty(x_106, x_107, x_34, x_34);
x_109 = lean_string_append(x_104, x_108);
lean_dec(x_108);
x_110 = lean_mk_string_unchecked(" of kind ", 9, 9);
x_111 = lean_string_append(x_109, x_110);
lean_dec(x_110);
lean_inc(x_1);
x_112 = l_Lean_Syntax_getKind(x_1);
x_113 = l_Lean_Name_toString(x_112, x_14, x_103);
x_114 = lean_string_append(x_111, x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_Lean_MessageData_ofFormat(x_115);
x_117 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_2, x_3, x_1, x_116);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_Syntax_getArg(x_98, x_34);
lean_dec(x_98);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_54 = x_119;
goto block_97;
}
}
else
{
lean_object* x_120; 
lean_dec(x_98);
x_120 = lean_box(0);
x_54 = x_120;
goto block_97;
}
block_53:
{
lean_object* x_38; 
lean_inc(x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__10), 15, 14);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_34);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_37);
lean_closure_set(x_38, 4, x_5);
lean_closure_set(x_38, 5, x_6);
lean_closure_set(x_38, 6, x_7);
lean_closure_set(x_38, 7, x_9);
lean_closure_set(x_38, 8, x_10);
lean_closure_set(x_38, 9, x_11);
lean_closure_set(x_38, 10, x_2);
lean_closure_set(x_38, 11, x_3);
lean_closure_set(x_38, 12, x_36);
lean_closure_set(x_38, 13, x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__9), 2, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_apply_2(x_4, lean_box(0), x_35);
x_41 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_40, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
x_43 = lean_mk_string_unchecked("terminationBy\?", 14, 14);
x_44 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_43);
x_45 = l_Lean_Syntax_isOfKind(x_42, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__9), 2, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_box(0);
x_48 = lean_apply_2(x_4, lean_box(0), x_47);
x_49 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_48, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__9), 2, 1);
lean_closure_set(x_50, 0, x_38);
x_51 = lean_apply_2(x_4, lean_box(0), x_35);
x_52 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_51, x_50);
return x_52;
}
}
}
block_97:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = l_Lean_Syntax_getArg(x_1, x_55);
x_57 = l_Lean_Syntax_isNone(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_inc(x_56);
x_58 = l_Lean_Syntax_matchesNull(x_56, x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = lean_box(x_58);
x_60 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_mk_string_unchecked("Unexpected Termination.suffix syntax: ", 38, 38);
x_62 = lean_box(0);
lean_inc(x_1);
x_63 = l_Lean_Syntax_formatStx(x_1, x_62, x_58);
x_64 = lean_unsigned_to_nat(120u);
x_65 = lean_format_pretty(x_63, x_64, x_34, x_34);
x_66 = lean_string_append(x_61, x_65);
lean_dec(x_65);
x_67 = lean_mk_string_unchecked(" of kind ", 9, 9);
x_68 = lean_string_append(x_66, x_67);
lean_dec(x_67);
lean_inc(x_1);
x_69 = l_Lean_Syntax_getKind(x_1);
x_70 = l_Lean_Name_toString(x_69, x_14, x_60);
x_71 = lean_string_append(x_68, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_MessageData_ofFormat(x_72);
x_74 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_2, x_3, x_1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = l_Lean_Syntax_getArg(x_56, x_34);
lean_dec(x_56);
x_76 = lean_mk_string_unchecked("decreasingBy", 12, 12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_77 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_76);
lean_inc(x_75);
x_78 = l_Lean_Syntax_isOfKind(x_75, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_75);
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = lean_box(x_78);
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_80, 0, x_79);
x_81 = lean_mk_string_unchecked("Unexpected Termination.suffix syntax: ", 38, 38);
x_82 = lean_box(0);
lean_inc(x_1);
x_83 = l_Lean_Syntax_formatStx(x_1, x_82, x_78);
x_84 = lean_unsigned_to_nat(120u);
x_85 = lean_format_pretty(x_83, x_84, x_34, x_34);
x_86 = lean_string_append(x_81, x_85);
lean_dec(x_85);
x_87 = lean_mk_string_unchecked(" of kind ", 9, 9);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
lean_inc(x_1);
x_89 = l_Lean_Syntax_getKind(x_1);
x_90 = l_Lean_Name_toString(x_89, x_58, x_80);
x_91 = lean_string_append(x_88, x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_MessageData_ofFormat(x_92);
x_94 = l_Lean_throwErrorAt(lean_box(0), lean_box(0), x_2, x_3, x_1, x_93);
return x_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_75);
x_35 = x_54;
x_36 = x_55;
x_37 = x_95;
goto block_53;
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_56);
x_96 = lean_box(0);
x_35 = x_54;
x_36 = x_55;
x_37 = x_96;
goto block_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_TerminationHints_none;
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 5);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
x_13 = lean_apply_2(x_5, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__0), 1, 0);
lean_inc(x_16);
lean_inc(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___redArg___lam__17___boxed), 8, 7);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_15);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_14);
lean_closure_set(x_18, 6, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_15, lean_box(0), x_19);
x_21 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabTerminationHints___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_elabTerminationHints___redArg___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_elabTerminationHints___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabTerminationHints___redArg___lam__19(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_elabTerminationHints___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_Elab_elabTerminationHints___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Elab_elabTerminationHints___redArg___lam__8(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___redArg___lam__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabTerminationHints___redArg___lam__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_TerminationHint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedTerminationBy = _init_l_Lean_Elab_instInhabitedTerminationBy();
lean_mark_persistent(l_Lean_Elab_instInhabitedTerminationBy);
l_Lean_Elab_instInhabitedDecreasingBy = _init_l_Lean_Elab_instInhabitedDecreasingBy();
lean_mark_persistent(l_Lean_Elab_instInhabitedDecreasingBy);
l_Lean_Elab_instInhabitedPartialFixpointType = _init_l_Lean_Elab_instInhabitedPartialFixpointType();
l_Lean_Elab_instInhabitedPartialFixpoint = _init_l_Lean_Elab_instInhabitedPartialFixpoint();
lean_mark_persistent(l_Lean_Elab_instInhabitedPartialFixpoint);
l_Lean_Elab_instInhabitedTerminationHints = _init_l_Lean_Elab_instInhabitedTerminationHints();
lean_mark_persistent(l_Lean_Elab_instInhabitedTerminationHints);
l_Lean_Elab_TerminationHints_none = _init_l_Lean_Elab_TerminationHints_none();
lean_mark_persistent(l_Lean_Elab_TerminationHints_none);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
