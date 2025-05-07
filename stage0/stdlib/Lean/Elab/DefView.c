// Lean compiler output
// Module: Lean.Elab.DefView
// Imports: Lean.Elab.Command Lean.Elab.DeclNameGen Lean.Elab.DeclUtil
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_DefView_isInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Command_mkInstanceName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_3017_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Modifiers_addAttr(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_2978_(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg___lam__0(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object*, lean_object*);
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx___boxed(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_isInstance(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_instInhabitedDefKind;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedDefView;
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg___lam__0___boxed(lean_object*);
lean_object* l_Lean_Elab_expandOptNamedPrio___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instTypeNameDefsParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_isInstance___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instImpl____x40_Lean_Elab_DefView___hyg_597_;
lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_18_(uint8_t, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_DefView_isInstance_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instBEqDefKind;
lean_object* l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedDefViewElabHeaderData;
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_18____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx(uint8_t x_1) {
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_DefKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_DefKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_DefKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_DefKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_DefKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Elab_instInhabitedDefKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_18_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Elab_DefKind_toCtorIdx(x_1);
x_4 = l_Lean_Elab_DefKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_18_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_instBEqDefKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_DefView_0__Lean_Elab_beqDefKind____x40_Lean_Elab_DefView___hyg_18____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isTheorem(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefKind_isExample(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 3)
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
LEAN_EXPORT lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isExample(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty(lean_box(0));
x_4 = lean_box(0);
x_5 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_3);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = l_Array_empty(lean_box(0));
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_usize_of_nat(x_6);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set_usize(x_8, 4, x_7);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_uint64_of_nat(x_6);
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_5);
lean_ctor_set(x_16, 3, x_5);
lean_ctor_set_usize(x_16, 4, x_7);
x_17 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint64(x_17, sizeof(void*)*1, x_14);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_19; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_19 = lean_ctor_get(x_2, 4);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
x_4 = x_21;
goto block_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go), 1, 0);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Language_SnapshotTask_map___redArg(x_22, x_23, x_24, x_25, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_28);
x_4 = x_31;
goto block_18;
}
block_18:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_2, 6);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Language_SnapshotTask_map___redArg(x_5, x_1, x_6, x_7, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_array_push(x_12, x_10);
x_14 = l_Array_append(lean_box(0), x_4, x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 7);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Array_append(lean_box(0), x_14, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instImpl____x40_Lean_Elab_DefView___hyg_597_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("DefsParsedSnapshot", 18, 18);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instTypeNameDefsParsedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instImpl____x40_Lean_Elab_DefView___hyg_597_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = l_Array_empty(lean_box(0));
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_usize_of_nat(x_7);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set_usize(x_9, 4, x_8);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_uint64_of_nat(x_7);
lean_inc(x_4);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
lean_inc(x_4);
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set(x_17, 3, x_6);
lean_ctor_set_usize(x_17, 4, x_8);
x_18 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_uint64(x_18, sizeof(void*)*1, x_15);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_unbox(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_40; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_40 = lean_ctor_get(x_23, 4);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_mk_empty_array_with_capacity(x_41);
x_25 = x_42;
goto block_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go), 1, 0);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_box(1);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Language_SnapshotTask_map___redArg(x_43, x_44, x_45, x_46, x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_mk_empty_array_with_capacity(x_50);
x_52 = lean_array_push(x_51, x_49);
x_25 = x_52;
goto block_39;
}
block_39:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_23, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_box(1);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Language_SnapshotTask_map___redArg(x_26, x_1, x_27, x_28, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_empty_array_with_capacity(x_32);
x_34 = lean_array_push(x_33, x_31);
x_35 = l_Array_append(lean_box(0), x_25, x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_23, 7);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l_Array_append(lean_box(0), x_35, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_Language_SnapshotTask_map___redArg(x_3, x_1, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_array_size(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_14, x_1, x_15, x_17, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot___lam__2), 2, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedDefView() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_10);
x_11 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_11);
x_12 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 3, x_12);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_2);
lean_ctor_set(x_15, 4, x_2);
lean_ctor_set(x_15, 5, x_3);
lean_ctor_set(x_15, 6, x_2);
lean_ctor_set(x_15, 7, x_13);
lean_ctor_set(x_15, 8, x_14);
x_16 = lean_unbox(x_1);
lean_ctor_set_uint8(x_15, sizeof(void*)*9, x_16);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_DefView_isInstance_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_mk_string_unchecked("instance", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_name_eq(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
goto _start;
}
else
{
return x_9;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_DefView_isInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lean_Elab_DefView_isInstance_spec__0(x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_DefView_isInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Elab_DefView_isInstance_spec__0(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DefView_isInstance___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_DefView_isInstance(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandOptDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("inline", 6, 6);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unbox(x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_13);
x_14 = l_Lean_Elab_Modifiers_addAttr(x_1, x_12);
x_15 = lean_mk_string_unchecked("reducible", 9, 9);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
x_18 = lean_unbox(x_8);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_18);
x_19 = l_Lean_Elab_Modifiers_addAttr(x_14, x_17);
x_20 = lean_box(5);
x_21 = l_Lean_Syntax_getArgs(x_2);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Array_toSubarray___redArg(x_21, x_22, x_23);
x_25 = l_Array_ofSubarray___redArg(x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("null", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_box(2);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Syntax_getArg(x_2, x_30);
x_32 = l_Lean_Syntax_getArg(x_2, x_23);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_19);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_6);
lean_ctor_set(x_35, 5, x_7);
lean_ctor_set(x_35, 6, x_32);
lean_ctor_set(x_35, 7, x_33);
lean_ctor_set(x_35, 8, x_34);
x_36 = lean_unbox(x_20);
lean_ctor_set_uint8(x_35, sizeof(void*)*9, x_36);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandOptDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_2, x_26);
x_28 = l_Lean_Syntax_isNone(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_27, x_29);
lean_dec(x_27);
x_31 = l_Lean_Syntax_getSepArgs(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_8 = x_32;
goto block_25;
}
else
{
lean_object* x_33; 
lean_dec(x_27);
x_33 = lean_box(0);
x_8 = x_33;
goto block_25;
}
block_25:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = lean_box(0);
x_10 = l_Lean_Syntax_getArgs(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Array_toSubarray___redArg(x_10, x_11, x_12);
x_14 = l_Array_ofSubarray___redArg(x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("null", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_2, x_19);
x_21 = l_Lean_Syntax_getArg(x_2, x_12);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_1);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_6);
lean_ctor_set(x_23, 5, x_7);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
lean_ctor_set(x_23, 8, x_8);
x_24 = lean_unbox(x_9);
lean_ctor_set_uint8(x_23, sizeof(void*)*9, x_24);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(2);
x_9 = l_Lean_Syntax_getArgs(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Array_toSubarray___redArg(x_9, x_10, x_11);
x_13 = l_Array_ofSubarray___redArg(x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("null", 4, 4);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_box(2);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_13);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_7);
x_21 = l_Lean_Syntax_getArg(x_2, x_11);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_6);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
lean_ctor_set(x_24, 8, x_23);
x_25 = lean_unbox(x_8);
lean_ctor_set_uint8(x_24, sizeof(void*)*9, x_25);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_12 = lean_box(1);
x_13 = l_Lean_Syntax_getArgs(x_1);
x_14 = lean_unsigned_to_nat(5u);
x_15 = l_Array_toSubarray___redArg(x_13, x_2, x_14);
x_16 = l_Array_ofSubarray___redArg(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_5);
x_19 = l_Lean_Syntax_getArg(x_1, x_14);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set(x_22, 3, x_8);
lean_ctor_set(x_22, 4, x_7);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_ctor_set(x_22, 8, x_21);
x_23 = lean_unbox(x_12);
lean_ctor_set_uint8(x_22, sizeof(void*)*9, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_expandOptNamedPrio___boxed), 3, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1(lean_box(0), x_14, x_3, x_4, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_getRef(x_3, x_4, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Command_getMainModule___redArg(x_4, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_28 = lean_unsigned_to_nat(4u);
x_29 = l_Lean_Syntax_getArg(x_2, x_28);
x_30 = l_Lean_Elab_expandDeclSig(x_29);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_box(0);
x_35 = lean_mk_string_unchecked("Attr", 4, 4);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = lean_box(2);
x_38 = l_Lean_Syntax_mkNumLit(x_27, x_37);
x_39 = lean_unbox(x_34);
x_40 = l_Lean_SourceInfo_fromRef(x_19, x_39);
lean_dec(x_19);
x_41 = lean_mk_string_unchecked("Lean", 4, 4);
x_42 = lean_mk_string_unchecked("Parser", 6, 6);
x_43 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
x_44 = l_Lean_Name_mkStr4(x_41, x_42, x_35, x_43);
lean_inc(x_43);
lean_inc(x_40);
lean_ctor_set_tag(x_30, 2);
lean_ctor_set(x_30, 1, x_43);
lean_ctor_set(x_30, 0, x_40);
x_45 = l_Lean_Name_mkStr1(x_36);
lean_inc(x_45);
lean_inc(x_40);
x_46 = l_Lean_Syntax_node1(x_40, x_45, x_38);
x_47 = l_Lean_Syntax_node2(x_40, x_44, x_30, x_46);
lean_inc(x_43);
x_48 = l_Lean_Name_mkStr1(x_43);
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_50);
x_51 = l_Lean_Elab_Modifiers_addAttr(x_1, x_49);
x_52 = lean_unsigned_to_nat(3u);
x_53 = l_Lean_Syntax_getArg(x_2, x_52);
x_54 = l_Lean_Syntax_getOptional_x3f(x_53);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_free_object(x_23);
x_55 = l_Lean_Syntax_getArgs(x_32);
lean_inc(x_33);
x_56 = l_Lean_Elab_Command_mkInstanceName(x_55, x_33, x_3, x_4, x_25);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_78 = lean_mk_string_unchecked("Elab", 4, 4);
x_79 = lean_mk_string_unchecked("mkInstanceName", 14, 14);
x_80 = l_Lean_Name_mkStr3(x_78, x_43, x_79);
lean_inc(x_80);
x_81 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_80, x_4, x_58);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_59 = x_3;
x_60 = x_4;
x_61 = x_84;
goto block_77;
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_81, 1);
x_87 = lean_ctor_get(x_81, 0);
lean_dec(x_87);
x_88 = l_Lean_Elab_Command_getScope___redArg(x_4, x_86);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
x_92 = lean_ctor_get(x_90, 2);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_mk_string_unchecked("generated ", 10, 10);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
lean_inc(x_57);
x_95 = l_Lean_Name_append(x_92, x_57);
x_96 = l_Lean_MessageData_ofName(x_95);
lean_ctor_set_tag(x_88, 7);
lean_ctor_set(x_88, 1, x_96);
lean_ctor_set(x_88, 0, x_94);
x_97 = lean_mk_string_unchecked("", 0, 0);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_98);
lean_ctor_set(x_81, 0, x_88);
x_99 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_80, x_81, x_3, x_4, x_91);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_59 = x_3;
x_60 = x_4;
x_61 = x_100;
goto block_77;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_88, 0);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_88);
x_103 = lean_ctor_get(x_101, 2);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_mk_string_unchecked("generated ", 10, 10);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
lean_inc(x_57);
x_106 = l_Lean_Name_append(x_103, x_57);
x_107 = l_Lean_MessageData_ofName(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("", 0, 0);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_110);
lean_ctor_set(x_81, 0, x_108);
x_111 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_80, x_81, x_3, x_4, x_102);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_59 = x_3;
x_60 = x_4;
x_61 = x_112;
goto block_77;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_113 = lean_ctor_get(x_81, 1);
lean_inc(x_113);
lean_dec(x_81);
x_114 = l_Lean_Elab_Command_getScope___redArg(x_4, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_115, 2);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_mk_string_unchecked("generated ", 10, 10);
x_120 = l_Lean_stringToMessageData(x_119);
lean_dec(x_119);
lean_inc(x_57);
x_121 = l_Lean_Name_append(x_118, x_57);
x_122 = l_Lean_MessageData_ofName(x_121);
if (lean_is_scalar(x_117)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_117;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_mk_string_unchecked("", 0, 0);
x_125 = l_Lean_stringToMessageData(x_124);
lean_dec(x_124);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_80, x_126, x_3, x_4, x_116);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_59 = x_3;
x_60 = x_4;
x_61 = x_128;
goto block_77;
}
}
block_77:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_mk_string_unchecked("Command", 7, 7);
x_63 = lean_mk_string_unchecked("declId", 6, 6);
x_64 = l_Lean_Name_mkStr4(x_41, x_42, x_62, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = l_Lean_Syntax_getArg(x_2, x_65);
x_67 = lean_box(1);
x_68 = lean_unbox(x_67);
x_69 = l_Lean_mkIdentFrom(x_66, x_57, x_68);
lean_dec(x_66);
x_70 = l_Array_empty(lean_box(0));
lean_inc(x_45);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_45);
lean_ctor_set(x_71, 2, x_70);
x_72 = lean_mk_empty_array_with_capacity(x_12);
x_73 = lean_array_push(x_72, x_69);
x_74 = lean_array_push(x_73, x_71);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_74);
x_76 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_75, x_59, x_60, x_61);
return x_76;
}
}
else
{
uint8_t x_129; 
lean_dec(x_51);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_56);
if (x_129 == 0)
{
return x_56;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_56, 0);
x_131 = lean_ctor_get(x_56, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_56);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_42);
lean_dec(x_41);
x_133 = lean_ctor_get(x_54, 0);
lean_inc(x_133);
lean_dec(x_54);
x_134 = lean_mk_string_unchecked("Elab", 4, 4);
x_135 = lean_mk_string_unchecked("mkInstanceName", 14, 14);
x_136 = l_Lean_Name_mkStr3(x_134, x_43, x_135);
lean_inc(x_136);
x_137 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_136, x_4, x_25);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_136);
lean_free_object(x_23);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_133, x_3, x_4, x_140);
return x_141;
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_137);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_137, 1);
x_144 = lean_ctor_get(x_137, 0);
lean_dec(x_144);
x_145 = l_Lean_Syntax_getArgs(x_32);
lean_inc(x_33);
x_146 = l_Lean_Elab_Command_mkInstanceName(x_145, x_33, x_3, x_4, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
lean_inc(x_136);
x_149 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_136, x_4, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_147);
lean_free_object(x_137);
lean_dec(x_136);
lean_free_object(x_23);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_133, x_3, x_4, x_152);
return x_153;
}
else
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_149);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_155 = lean_ctor_get(x_149, 1);
x_156 = lean_ctor_get(x_149, 0);
lean_dec(x_156);
x_157 = l_Lean_Elab_Command_getScope___redArg(x_4, x_155);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = lean_ctor_get(x_157, 1);
x_161 = lean_ctor_get(x_159, 2);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_mk_string_unchecked("generated ", 10, 10);
x_163 = l_Lean_stringToMessageData(x_162);
lean_dec(x_162);
x_164 = l_Lean_Name_append(x_161, x_147);
x_165 = l_Lean_MessageData_ofName(x_164);
lean_ctor_set_tag(x_157, 7);
lean_ctor_set(x_157, 1, x_165);
lean_ctor_set(x_157, 0, x_163);
x_166 = lean_mk_string_unchecked(" for ", 5, 5);
x_167 = l_Lean_stringToMessageData(x_166);
lean_dec(x_166);
lean_ctor_set_tag(x_149, 7);
lean_ctor_set(x_149, 1, x_167);
lean_ctor_set(x_149, 0, x_157);
lean_inc(x_133);
x_168 = l_Lean_MessageData_ofSyntax(x_133);
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_168);
lean_ctor_set(x_137, 0, x_149);
x_169 = lean_mk_string_unchecked("", 0, 0);
x_170 = l_Lean_stringToMessageData(x_169);
lean_dec(x_169);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_170);
lean_ctor_set(x_23, 0, x_137);
x_171 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_136, x_23, x_3, x_4, x_160);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_133, x_3, x_4, x_172);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_174 = lean_ctor_get(x_157, 0);
x_175 = lean_ctor_get(x_157, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_157);
x_176 = lean_ctor_get(x_174, 2);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_mk_string_unchecked("generated ", 10, 10);
x_178 = l_Lean_stringToMessageData(x_177);
lean_dec(x_177);
x_179 = l_Lean_Name_append(x_176, x_147);
x_180 = l_Lean_MessageData_ofName(x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_mk_string_unchecked(" for ", 5, 5);
x_183 = l_Lean_stringToMessageData(x_182);
lean_dec(x_182);
lean_ctor_set_tag(x_149, 7);
lean_ctor_set(x_149, 1, x_183);
lean_ctor_set(x_149, 0, x_181);
lean_inc(x_133);
x_184 = l_Lean_MessageData_ofSyntax(x_133);
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_184);
lean_ctor_set(x_137, 0, x_149);
x_185 = lean_mk_string_unchecked("", 0, 0);
x_186 = l_Lean_stringToMessageData(x_185);
lean_dec(x_185);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_186);
lean_ctor_set(x_23, 0, x_137);
x_187 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_136, x_23, x_3, x_4, x_175);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_133, x_3, x_4, x_188);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_190 = lean_ctor_get(x_149, 1);
lean_inc(x_190);
lean_dec(x_149);
x_191 = l_Lean_Elab_Command_getScope___redArg(x_4, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_192, 2);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_mk_string_unchecked("generated ", 10, 10);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = l_Lean_Name_append(x_195, x_147);
x_199 = l_Lean_MessageData_ofName(x_198);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(7, 2, 0);
} else {
 x_200 = x_194;
 lean_ctor_set_tag(x_200, 7);
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_mk_string_unchecked(" for ", 5, 5);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_202);
lean_inc(x_133);
x_204 = l_Lean_MessageData_ofSyntax(x_133);
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_204);
lean_ctor_set(x_137, 0, x_203);
x_205 = lean_mk_string_unchecked("", 0, 0);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_206);
lean_ctor_set(x_23, 0, x_137);
x_207 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_136, x_23, x_3, x_4, x_193);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_133, x_3, x_4, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_free_object(x_137);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_51);
lean_dec(x_45);
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_23);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_146);
if (x_210 == 0)
{
return x_146;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_146, 0);
x_212 = lean_ctor_get(x_146, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_146);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_137, 1);
lean_inc(x_214);
lean_dec(x_137);
x_215 = l_Lean_Syntax_getArgs(x_32);
lean_inc(x_33);
x_216 = l_Lean_Elab_Command_mkInstanceName(x_215, x_33, x_3, x_4, x_214);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_136);
x_219 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_136, x_4, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_unbox(x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_217);
lean_dec(x_136);
lean_free_object(x_23);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_133, x_3, x_4, x_222);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_225 = x_219;
} else {
 lean_dec_ref(x_219);
 x_225 = lean_box(0);
}
x_226 = l_Lean_Elab_Command_getScope___redArg(x_4, x_224);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_227, 2);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_mk_string_unchecked("generated ", 10, 10);
x_232 = l_Lean_stringToMessageData(x_231);
lean_dec(x_231);
x_233 = l_Lean_Name_append(x_230, x_217);
x_234 = l_Lean_MessageData_ofName(x_233);
if (lean_is_scalar(x_229)) {
 x_235 = lean_alloc_ctor(7, 2, 0);
} else {
 x_235 = x_229;
 lean_ctor_set_tag(x_235, 7);
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_mk_string_unchecked(" for ", 5, 5);
x_237 = l_Lean_stringToMessageData(x_236);
lean_dec(x_236);
if (lean_is_scalar(x_225)) {
 x_238 = lean_alloc_ctor(7, 2, 0);
} else {
 x_238 = x_225;
 lean_ctor_set_tag(x_238, 7);
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_133);
x_239 = l_Lean_MessageData_ofSyntax(x_133);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_mk_string_unchecked("", 0, 0);
x_242 = l_Lean_stringToMessageData(x_241);
lean_dec(x_241);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_242);
lean_ctor_set(x_23, 0, x_240);
x_243 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_136, x_23, x_3, x_4, x_228);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_37, x_45, x_33, x_51, x_32, x_133, x_3, x_4, x_244);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_51);
lean_dec(x_45);
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_23);
lean_dec(x_2);
x_246 = lean_ctor_get(x_216, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_216, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_248 = x_216;
} else {
 lean_dec_ref(x_216);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_250 = lean_ctor_get(x_30, 0);
x_251 = lean_ctor_get(x_30, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_30);
x_252 = lean_box(0);
x_253 = lean_mk_string_unchecked("Attr", 4, 4);
x_254 = lean_mk_string_unchecked("null", 4, 4);
x_255 = lean_box(2);
x_256 = l_Lean_Syntax_mkNumLit(x_27, x_255);
x_257 = lean_unbox(x_252);
x_258 = l_Lean_SourceInfo_fromRef(x_19, x_257);
lean_dec(x_19);
x_259 = lean_mk_string_unchecked("Lean", 4, 4);
x_260 = lean_mk_string_unchecked("Parser", 6, 6);
x_261 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
x_262 = l_Lean_Name_mkStr4(x_259, x_260, x_253, x_261);
lean_inc(x_261);
lean_inc(x_258);
x_263 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set(x_263, 1, x_261);
x_264 = l_Lean_Name_mkStr1(x_254);
lean_inc(x_264);
lean_inc(x_258);
x_265 = l_Lean_Syntax_node1(x_258, x_264, x_256);
x_266 = l_Lean_Syntax_node2(x_258, x_262, x_263, x_265);
lean_inc(x_261);
x_267 = l_Lean_Name_mkStr1(x_261);
x_268 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
x_269 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_268, sizeof(void*)*2, x_269);
x_270 = l_Lean_Elab_Modifiers_addAttr(x_1, x_268);
x_271 = lean_unsigned_to_nat(3u);
x_272 = l_Lean_Syntax_getArg(x_2, x_271);
x_273 = l_Lean_Syntax_getOptional_x3f(x_272);
lean_dec(x_272);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; 
lean_free_object(x_23);
x_274 = l_Lean_Syntax_getArgs(x_250);
lean_inc(x_251);
x_275 = l_Lean_Elab_Command_mkInstanceName(x_274, x_251, x_3, x_4, x_25);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_297 = lean_mk_string_unchecked("Elab", 4, 4);
x_298 = lean_mk_string_unchecked("mkInstanceName", 14, 14);
x_299 = l_Lean_Name_mkStr3(x_297, x_261, x_298);
lean_inc(x_299);
x_300 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_299, x_4, x_277);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_unbox(x_301);
lean_dec(x_301);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec(x_299);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_278 = x_3;
x_279 = x_4;
x_280 = x_303;
goto block_296;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_304 = lean_ctor_get(x_300, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_305 = x_300;
} else {
 lean_dec_ref(x_300);
 x_305 = lean_box(0);
}
x_306 = l_Lean_Elab_Command_getScope___redArg(x_4, x_304);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_309 = x_306;
} else {
 lean_dec_ref(x_306);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_307, 2);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_mk_string_unchecked("generated ", 10, 10);
x_312 = l_Lean_stringToMessageData(x_311);
lean_dec(x_311);
lean_inc(x_276);
x_313 = l_Lean_Name_append(x_310, x_276);
x_314 = l_Lean_MessageData_ofName(x_313);
if (lean_is_scalar(x_309)) {
 x_315 = lean_alloc_ctor(7, 2, 0);
} else {
 x_315 = x_309;
 lean_ctor_set_tag(x_315, 7);
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_mk_string_unchecked("", 0, 0);
x_317 = l_Lean_stringToMessageData(x_316);
lean_dec(x_316);
if (lean_is_scalar(x_305)) {
 x_318 = lean_alloc_ctor(7, 2, 0);
} else {
 x_318 = x_305;
 lean_ctor_set_tag(x_318, 7);
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_299, x_318, x_3, x_4, x_308);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_278 = x_3;
x_279 = x_4;
x_280 = x_320;
goto block_296;
}
block_296:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_281 = lean_mk_string_unchecked("Command", 7, 7);
x_282 = lean_mk_string_unchecked("declId", 6, 6);
x_283 = l_Lean_Name_mkStr4(x_259, x_260, x_281, x_282);
x_284 = lean_unsigned_to_nat(1u);
x_285 = l_Lean_Syntax_getArg(x_2, x_284);
x_286 = lean_box(1);
x_287 = lean_unbox(x_286);
x_288 = l_Lean_mkIdentFrom(x_285, x_276, x_287);
lean_dec(x_285);
x_289 = l_Array_empty(lean_box(0));
lean_inc(x_264);
x_290 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_290, 0, x_255);
lean_ctor_set(x_290, 1, x_264);
lean_ctor_set(x_290, 2, x_289);
x_291 = lean_mk_empty_array_with_capacity(x_12);
x_292 = lean_array_push(x_291, x_288);
x_293 = lean_array_push(x_292, x_290);
x_294 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_294, 0, x_255);
lean_ctor_set(x_294, 1, x_283);
lean_ctor_set(x_294, 2, x_293);
x_295 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_255, x_264, x_251, x_270, x_250, x_294, x_278, x_279, x_280);
return x_295;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_2);
x_321 = lean_ctor_get(x_275, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_275, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_323 = x_275;
} else {
 lean_dec_ref(x_275);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
lean_dec(x_260);
lean_dec(x_259);
x_325 = lean_ctor_get(x_273, 0);
lean_inc(x_325);
lean_dec(x_273);
x_326 = lean_mk_string_unchecked("Elab", 4, 4);
x_327 = lean_mk_string_unchecked("mkInstanceName", 14, 14);
x_328 = l_Lean_Name_mkStr3(x_326, x_261, x_327);
lean_inc(x_328);
x_329 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_328, x_4, x_25);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_unbox(x_330);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_328);
lean_free_object(x_23);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_255, x_264, x_251, x_270, x_250, x_325, x_3, x_4, x_332);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_ctor_get(x_329, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_335 = x_329;
} else {
 lean_dec_ref(x_329);
 x_335 = lean_box(0);
}
x_336 = l_Lean_Syntax_getArgs(x_250);
lean_inc(x_251);
x_337 = l_Lean_Elab_Command_mkInstanceName(x_336, x_251, x_3, x_4, x_334);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
lean_inc(x_328);
x_340 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_328, x_4, x_339);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_unbox(x_341);
lean_dec(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_338);
lean_dec(x_335);
lean_dec(x_328);
lean_free_object(x_23);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
lean_dec(x_340);
x_344 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_255, x_264, x_251, x_270, x_250, x_325, x_3, x_4, x_343);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_345 = lean_ctor_get(x_340, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_346 = x_340;
} else {
 lean_dec_ref(x_340);
 x_346 = lean_box(0);
}
x_347 = l_Lean_Elab_Command_getScope___redArg(x_4, x_345);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_350 = x_347;
} else {
 lean_dec_ref(x_347);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_348, 2);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_mk_string_unchecked("generated ", 10, 10);
x_353 = l_Lean_stringToMessageData(x_352);
lean_dec(x_352);
x_354 = l_Lean_Name_append(x_351, x_338);
x_355 = l_Lean_MessageData_ofName(x_354);
if (lean_is_scalar(x_350)) {
 x_356 = lean_alloc_ctor(7, 2, 0);
} else {
 x_356 = x_350;
 lean_ctor_set_tag(x_356, 7);
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_mk_string_unchecked(" for ", 5, 5);
x_358 = l_Lean_stringToMessageData(x_357);
lean_dec(x_357);
if (lean_is_scalar(x_346)) {
 x_359 = lean_alloc_ctor(7, 2, 0);
} else {
 x_359 = x_346;
 lean_ctor_set_tag(x_359, 7);
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_358);
lean_inc(x_325);
x_360 = l_Lean_MessageData_ofSyntax(x_325);
if (lean_is_scalar(x_335)) {
 x_361 = lean_alloc_ctor(7, 2, 0);
} else {
 x_361 = x_335;
 lean_ctor_set_tag(x_361, 7);
}
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_mk_string_unchecked("", 0, 0);
x_363 = l_Lean_stringToMessageData(x_362);
lean_dec(x_362);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_363);
lean_ctor_set(x_23, 0, x_361);
x_364 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_328, x_23, x_3, x_4, x_349);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_255, x_264, x_251, x_270, x_250, x_325, x_3, x_4, x_365);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_335);
lean_dec(x_328);
lean_dec(x_325);
lean_dec(x_270);
lean_dec(x_264);
lean_dec(x_251);
lean_dec(x_250);
lean_free_object(x_23);
lean_dec(x_2);
x_367 = lean_ctor_get(x_337, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_337, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_369 = x_337;
} else {
 lean_dec_ref(x_337);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_371 = lean_ctor_get(x_23, 1);
lean_inc(x_371);
lean_dec(x_23);
x_372 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_373 = lean_unsigned_to_nat(4u);
x_374 = l_Lean_Syntax_getArg(x_2, x_373);
x_375 = l_Lean_Elab_expandDeclSig(x_374);
lean_dec(x_374);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
x_379 = lean_box(0);
x_380 = lean_mk_string_unchecked("Attr", 4, 4);
x_381 = lean_mk_string_unchecked("null", 4, 4);
x_382 = lean_box(2);
x_383 = l_Lean_Syntax_mkNumLit(x_372, x_382);
x_384 = lean_unbox(x_379);
x_385 = l_Lean_SourceInfo_fromRef(x_19, x_384);
lean_dec(x_19);
x_386 = lean_mk_string_unchecked("Lean", 4, 4);
x_387 = lean_mk_string_unchecked("Parser", 6, 6);
x_388 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_388);
lean_inc(x_387);
lean_inc(x_386);
x_389 = l_Lean_Name_mkStr4(x_386, x_387, x_380, x_388);
lean_inc(x_388);
lean_inc(x_385);
if (lean_is_scalar(x_378)) {
 x_390 = lean_alloc_ctor(2, 2, 0);
} else {
 x_390 = x_378;
 lean_ctor_set_tag(x_390, 2);
}
lean_ctor_set(x_390, 0, x_385);
lean_ctor_set(x_390, 1, x_388);
x_391 = l_Lean_Name_mkStr1(x_381);
lean_inc(x_391);
lean_inc(x_385);
x_392 = l_Lean_Syntax_node1(x_385, x_391, x_383);
x_393 = l_Lean_Syntax_node2(x_385, x_389, x_390, x_392);
lean_inc(x_388);
x_394 = l_Lean_Name_mkStr1(x_388);
x_395 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
x_396 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_395, sizeof(void*)*2, x_396);
x_397 = l_Lean_Elab_Modifiers_addAttr(x_1, x_395);
x_398 = lean_unsigned_to_nat(3u);
x_399 = l_Lean_Syntax_getArg(x_2, x_398);
x_400 = l_Lean_Syntax_getOptional_x3f(x_399);
lean_dec(x_399);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = l_Lean_Syntax_getArgs(x_376);
lean_inc(x_377);
x_402 = l_Lean_Elab_Command_mkInstanceName(x_401, x_377, x_3, x_4, x_371);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_424 = lean_mk_string_unchecked("Elab", 4, 4);
x_425 = lean_mk_string_unchecked("mkInstanceName", 14, 14);
x_426 = l_Lean_Name_mkStr3(x_424, x_388, x_425);
lean_inc(x_426);
x_427 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_426, x_4, x_404);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_unbox(x_428);
lean_dec(x_428);
if (x_429 == 0)
{
lean_object* x_430; 
lean_dec(x_426);
x_430 = lean_ctor_get(x_427, 1);
lean_inc(x_430);
lean_dec(x_427);
x_405 = x_3;
x_406 = x_4;
x_407 = x_430;
goto block_423;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_431 = lean_ctor_get(x_427, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_432 = x_427;
} else {
 lean_dec_ref(x_427);
 x_432 = lean_box(0);
}
x_433 = l_Lean_Elab_Command_getScope___redArg(x_4, x_431);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_436 = x_433;
} else {
 lean_dec_ref(x_433);
 x_436 = lean_box(0);
}
x_437 = lean_ctor_get(x_434, 2);
lean_inc(x_437);
lean_dec(x_434);
x_438 = lean_mk_string_unchecked("generated ", 10, 10);
x_439 = l_Lean_stringToMessageData(x_438);
lean_dec(x_438);
lean_inc(x_403);
x_440 = l_Lean_Name_append(x_437, x_403);
x_441 = l_Lean_MessageData_ofName(x_440);
if (lean_is_scalar(x_436)) {
 x_442 = lean_alloc_ctor(7, 2, 0);
} else {
 x_442 = x_436;
 lean_ctor_set_tag(x_442, 7);
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_441);
x_443 = lean_mk_string_unchecked("", 0, 0);
x_444 = l_Lean_stringToMessageData(x_443);
lean_dec(x_443);
if (lean_is_scalar(x_432)) {
 x_445 = lean_alloc_ctor(7, 2, 0);
} else {
 x_445 = x_432;
 lean_ctor_set_tag(x_445, 7);
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_444);
x_446 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_426, x_445, x_3, x_4, x_435);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_405 = x_3;
x_406 = x_4;
x_407 = x_447;
goto block_423;
}
block_423:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_408 = lean_mk_string_unchecked("Command", 7, 7);
x_409 = lean_mk_string_unchecked("declId", 6, 6);
x_410 = l_Lean_Name_mkStr4(x_386, x_387, x_408, x_409);
x_411 = lean_unsigned_to_nat(1u);
x_412 = l_Lean_Syntax_getArg(x_2, x_411);
x_413 = lean_box(1);
x_414 = lean_unbox(x_413);
x_415 = l_Lean_mkIdentFrom(x_412, x_403, x_414);
lean_dec(x_412);
x_416 = l_Array_empty(lean_box(0));
lean_inc(x_391);
x_417 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_417, 0, x_382);
lean_ctor_set(x_417, 1, x_391);
lean_ctor_set(x_417, 2, x_416);
x_418 = lean_mk_empty_array_with_capacity(x_12);
x_419 = lean_array_push(x_418, x_415);
x_420 = lean_array_push(x_419, x_417);
x_421 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_421, 0, x_382);
lean_ctor_set(x_421, 1, x_410);
lean_ctor_set(x_421, 2, x_420);
x_422 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_382, x_391, x_377, x_397, x_376, x_421, x_405, x_406, x_407);
return x_422;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_397);
lean_dec(x_391);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_2);
x_448 = lean_ctor_get(x_402, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_402, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_450 = x_402;
} else {
 lean_dec_ref(x_402);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
lean_dec(x_387);
lean_dec(x_386);
x_452 = lean_ctor_get(x_400, 0);
lean_inc(x_452);
lean_dec(x_400);
x_453 = lean_mk_string_unchecked("Elab", 4, 4);
x_454 = lean_mk_string_unchecked("mkInstanceName", 14, 14);
x_455 = l_Lean_Name_mkStr3(x_453, x_388, x_454);
lean_inc(x_455);
x_456 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_455, x_4, x_371);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_unbox(x_457);
lean_dec(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; 
lean_dec(x_455);
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_dec(x_456);
x_460 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_382, x_391, x_377, x_397, x_376, x_452, x_3, x_4, x_459);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_461 = lean_ctor_get(x_456, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_462 = x_456;
} else {
 lean_dec_ref(x_456);
 x_462 = lean_box(0);
}
x_463 = l_Lean_Syntax_getArgs(x_376);
lean_inc(x_377);
x_464 = l_Lean_Elab_Command_mkInstanceName(x_463, x_377, x_3, x_4, x_461);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
lean_dec(x_464);
lean_inc(x_455);
x_467 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Command_runLinters_spec__6_spec__6___redArg(x_455, x_4, x_466);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_unbox(x_468);
lean_dec(x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_455);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec(x_467);
x_471 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_382, x_391, x_377, x_397, x_376, x_452, x_3, x_4, x_470);
return x_471;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_472 = lean_ctor_get(x_467, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_473 = x_467;
} else {
 lean_dec_ref(x_467);
 x_473 = lean_box(0);
}
x_474 = l_Lean_Elab_Command_getScope___redArg(x_4, x_472);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_477 = x_474;
} else {
 lean_dec_ref(x_474);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_475, 2);
lean_inc(x_478);
lean_dec(x_475);
x_479 = lean_mk_string_unchecked("generated ", 10, 10);
x_480 = l_Lean_stringToMessageData(x_479);
lean_dec(x_479);
x_481 = l_Lean_Name_append(x_478, x_465);
x_482 = l_Lean_MessageData_ofName(x_481);
if (lean_is_scalar(x_477)) {
 x_483 = lean_alloc_ctor(7, 2, 0);
} else {
 x_483 = x_477;
 lean_ctor_set_tag(x_483, 7);
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_482);
x_484 = lean_mk_string_unchecked(" for ", 5, 5);
x_485 = l_Lean_stringToMessageData(x_484);
lean_dec(x_484);
if (lean_is_scalar(x_473)) {
 x_486 = lean_alloc_ctor(7, 2, 0);
} else {
 x_486 = x_473;
 lean_ctor_set_tag(x_486, 7);
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_485);
lean_inc(x_452);
x_487 = l_Lean_MessageData_ofSyntax(x_452);
if (lean_is_scalar(x_462)) {
 x_488 = lean_alloc_ctor(7, 2, 0);
} else {
 x_488 = x_462;
 lean_ctor_set_tag(x_488, 7);
}
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_489 = lean_mk_string_unchecked("", 0, 0);
x_490 = l_Lean_stringToMessageData(x_489);
lean_dec(x_489);
x_491 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_490);
x_492 = l_Lean_addTrace___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__1(x_455, x_491, x_3, x_4, x_476);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
x_494 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_2, x_6, x_382, x_391, x_377, x_397, x_376, x_452, x_3, x_4, x_493);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_462);
lean_dec(x_455);
lean_dec(x_452);
lean_dec(x_397);
lean_dec(x_391);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_2);
x_495 = lean_ctor_get(x_464, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_464, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_497 = x_464;
} else {
 lean_dec_ref(x_464);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
}
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_499 = !lean_is_exclusive(x_15);
if (x_499 == 0)
{
return x_15;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_15, 0);
x_501 = lean_ctor_get(x_15, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_15);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
else
{
uint8_t x_503; 
lean_dec(x_2);
lean_dec(x_1);
x_503 = !lean_is_exclusive(x_9);
if (x_503 == 0)
{
return x_9;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_9, 0);
x_505 = lean_ctor_get(x_9, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_9);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_mkDefViewOfInstance___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefViewOfInstance(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_9 = lean_box(4);
x_10 = l_Lean_Syntax_getArgs(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Array_toSubarray___redArg(x_10, x_11, x_12);
x_14 = l_Array_ofSubarray___redArg(x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("null", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_box(2);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_4);
lean_ctor_set(x_24, 5, x_21);
lean_ctor_set(x_24, 6, x_5);
lean_ctor_set(x_24, 7, x_22);
lean_ctor_set(x_24, 8, x_23);
x_25 = lean_unbox(x_9);
lean_ctor_set_uint8(x_24, sizeof(void*)*9, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_65 = lean_unsigned_to_nat(3u);
x_66 = l_Lean_Syntax_getArg(x_2, x_65);
x_67 = l_Lean_Syntax_getOptional_x3f(x_66);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 3);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_69 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Elab_Command_getMainModule___redArg(x_4, x_73);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_ctor_get(x_74, 1);
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = l_Lean_SourceInfo_fromRef(x_70, x_68);
lean_dec(x_70);
x_79 = lean_mk_string_unchecked("Lean", 4, 4);
x_80 = lean_mk_string_unchecked("Parser", 6, 6);
x_81 = lean_mk_string_unchecked("Term", 4, 4);
x_82 = lean_mk_string_unchecked("defaultOrOfNonempty", 19, 19);
x_83 = l_Lean_Name_mkStr4(x_79, x_80, x_81, x_82);
x_84 = lean_mk_string_unchecked("default_or_ofNonempty%", 22, 22);
lean_inc(x_78);
lean_ctor_set_tag(x_74, 2);
lean_ctor_set(x_74, 1, x_84);
lean_ctor_set(x_74, 0, x_78);
x_85 = lean_mk_string_unchecked("null", 4, 4);
x_86 = l_Lean_Name_mkStr1(x_85);
x_87 = l_Array_mkArray0(lean_box(0));
lean_inc(x_78);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_87);
x_89 = l_Lean_Syntax_node2(x_78, x_83, x_74, x_88);
x_11 = x_89;
x_12 = x_3;
x_13 = x_4;
x_14 = x_76;
goto block_64;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_ctor_get(x_74, 1);
lean_inc(x_90);
lean_dec(x_74);
x_91 = l_Lean_SourceInfo_fromRef(x_70, x_68);
lean_dec(x_70);
x_92 = lean_mk_string_unchecked("Lean", 4, 4);
x_93 = lean_mk_string_unchecked("Parser", 6, 6);
x_94 = lean_mk_string_unchecked("Term", 4, 4);
x_95 = lean_mk_string_unchecked("defaultOrOfNonempty", 19, 19);
x_96 = l_Lean_Name_mkStr4(x_92, x_93, x_94, x_95);
x_97 = lean_mk_string_unchecked("default_or_ofNonempty%", 22, 22);
lean_inc(x_91);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_mk_string_unchecked("null", 4, 4);
x_100 = l_Lean_Name_mkStr1(x_99);
x_101 = l_Array_mkArray0(lean_box(0));
lean_inc(x_91);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_101);
x_103 = l_Lean_Syntax_node2(x_91, x_96, x_98, x_102);
x_11 = x_103;
x_12 = x_3;
x_13 = x_4;
x_14 = x_90;
goto block_64;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_106);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_107, 1);
x_110 = lean_ctor_get(x_107, 0);
lean_dec(x_110);
x_111 = l_Lean_Elab_Command_getMainModule___redArg(x_4, x_109);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_113 = lean_ctor_get(x_111, 1);
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
x_115 = lean_box(0);
x_116 = lean_unbox(x_115);
x_117 = l_Lean_SourceInfo_fromRef(x_105, x_116);
lean_dec(x_105);
x_118 = lean_mk_string_unchecked("Lean", 4, 4);
x_119 = lean_mk_string_unchecked("Parser", 6, 6);
x_120 = lean_mk_string_unchecked("Term", 4, 4);
x_121 = lean_mk_string_unchecked("defaultOrOfNonempty", 19, 19);
x_122 = l_Lean_Name_mkStr4(x_118, x_119, x_120, x_121);
x_123 = lean_mk_string_unchecked("default_or_ofNonempty%", 22, 22);
lean_inc(x_117);
lean_ctor_set_tag(x_111, 2);
lean_ctor_set(x_111, 1, x_123);
lean_ctor_set(x_111, 0, x_117);
x_124 = lean_mk_string_unchecked("null", 4, 4);
x_125 = l_Lean_Name_mkStr1(x_124);
x_126 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_117);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_126);
lean_ctor_set(x_107, 0, x_117);
lean_inc(x_117);
x_127 = l_Lean_Syntax_node1(x_117, x_125, x_107);
x_128 = l_Lean_Syntax_node2(x_117, x_122, x_111, x_127);
x_11 = x_128;
x_12 = x_3;
x_13 = x_4;
x_14 = x_113;
goto block_64;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
lean_dec(x_111);
x_130 = lean_box(0);
x_131 = lean_unbox(x_130);
x_132 = l_Lean_SourceInfo_fromRef(x_105, x_131);
lean_dec(x_105);
x_133 = lean_mk_string_unchecked("Lean", 4, 4);
x_134 = lean_mk_string_unchecked("Parser", 6, 6);
x_135 = lean_mk_string_unchecked("Term", 4, 4);
x_136 = lean_mk_string_unchecked("defaultOrOfNonempty", 19, 19);
x_137 = l_Lean_Name_mkStr4(x_133, x_134, x_135, x_136);
x_138 = lean_mk_string_unchecked("default_or_ofNonempty%", 22, 22);
lean_inc(x_132);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked("null", 4, 4);
x_141 = l_Lean_Name_mkStr1(x_140);
x_142 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_132);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_142);
lean_ctor_set(x_107, 0, x_132);
lean_inc(x_132);
x_143 = l_Lean_Syntax_node1(x_132, x_141, x_107);
x_144 = l_Lean_Syntax_node2(x_132, x_137, x_139, x_143);
x_11 = x_144;
x_12 = x_3;
x_13 = x_4;
x_14 = x_129;
goto block_64;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_145 = lean_ctor_get(x_107, 1);
lean_inc(x_145);
lean_dec(x_107);
x_146 = l_Lean_Elab_Command_getMainModule___redArg(x_4, x_145);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_box(0);
x_150 = lean_unbox(x_149);
x_151 = l_Lean_SourceInfo_fromRef(x_105, x_150);
lean_dec(x_105);
x_152 = lean_mk_string_unchecked("Lean", 4, 4);
x_153 = lean_mk_string_unchecked("Parser", 6, 6);
x_154 = lean_mk_string_unchecked("Term", 4, 4);
x_155 = lean_mk_string_unchecked("defaultOrOfNonempty", 19, 19);
x_156 = l_Lean_Name_mkStr4(x_152, x_153, x_154, x_155);
x_157 = lean_mk_string_unchecked("default_or_ofNonempty%", 22, 22);
lean_inc(x_151);
if (lean_is_scalar(x_148)) {
 x_158 = lean_alloc_ctor(2, 2, 0);
} else {
 x_158 = x_148;
 lean_ctor_set_tag(x_158, 2);
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_mk_string_unchecked("null", 4, 4);
x_160 = l_Lean_Name_mkStr1(x_159);
x_161 = lean_mk_string_unchecked("unsafe", 6, 6);
lean_inc(x_151);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_161);
lean_inc(x_151);
x_163 = l_Lean_Syntax_node1(x_151, x_160, x_162);
x_164 = l_Lean_Syntax_node2(x_151, x_156, x_158, x_163);
x_11 = x_164;
x_12 = x_3;
x_13 = x_4;
x_14 = x_147;
goto block_64;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_67, 0);
lean_inc(x_165);
lean_dec(x_67);
x_166 = l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0(x_2, x_10, x_1, x_9, x_165, x_3, x_4, x_5);
return x_166;
}
block_64:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = l_Lean_Elab_Command_getRef(x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_getCurrMacroScope(x_12, x_13, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Command_getMainModule___redArg(x_13, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_SourceInfo_fromRef(x_16, x_25);
lean_dec(x_16);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Parser", 6, 6);
x_29 = lean_mk_string_unchecked("Command", 7, 7);
x_30 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_28);
lean_inc(x_27);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
x_32 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_26);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_32);
lean_ctor_set(x_20, 0, x_26);
x_33 = lean_mk_string_unchecked("Termination", 11, 11);
x_34 = lean_mk_string_unchecked("suffix", 6, 6);
x_35 = l_Lean_Name_mkStr4(x_27, x_28, x_33, x_34);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = l_Array_mkArray0(lean_box(0));
lean_inc(x_26);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
lean_inc_n(x_39, 2);
lean_inc(x_26);
x_40 = l_Lean_Syntax_node2(x_26, x_35, x_39, x_39);
x_41 = l_Lean_Syntax_node4(x_26, x_31, x_20, x_11, x_40, x_39);
x_42 = l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0(x_2, x_10, x_1, x_9, x_41, x_12, x_13, x_22);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
x_46 = l_Lean_SourceInfo_fromRef(x_16, x_45);
lean_dec(x_16);
x_47 = lean_mk_string_unchecked("Lean", 4, 4);
x_48 = lean_mk_string_unchecked("Parser", 6, 6);
x_49 = lean_mk_string_unchecked("Command", 7, 7);
x_50 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_48);
lean_inc(x_47);
x_51 = l_Lean_Name_mkStr4(x_47, x_48, x_49, x_50);
x_52 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_46);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_mk_string_unchecked("Termination", 11, 11);
x_55 = lean_mk_string_unchecked("suffix", 6, 6);
x_56 = l_Lean_Name_mkStr4(x_47, x_48, x_54, x_55);
x_57 = lean_mk_string_unchecked("null", 4, 4);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = l_Array_mkArray0(lean_box(0));
lean_inc(x_46);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_59);
lean_inc_n(x_60, 2);
lean_inc(x_46);
x_61 = l_Lean_Syntax_node2(x_46, x_56, x_60, x_60);
x_62 = l_Lean_Syntax_node4(x_46, x_51, x_53, x_11, x_61, x_60);
x_63 = l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0(x_2, x_10, x_1, x_9, x_62, x_12, x_13, x_43);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_mkDefViewOfOpaque___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfOpaque___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefViewOfOpaque(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandOptDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = lean_mk_string_unchecked("_example", 8, 8);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_box(1);
x_13 = lean_mk_string_unchecked("Lean", 4, 4);
x_14 = lean_mk_string_unchecked("Parser", 6, 6);
x_15 = lean_mk_string_unchecked("Command", 7, 7);
x_16 = lean_mk_string_unchecked("declId", 6, 6);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
x_18 = lean_unbox(x_12);
x_19 = l_Lean_mkIdentFrom(x_9, x_11, x_18);
lean_dec(x_9);
x_20 = l_Array_empty(lean_box(0));
x_21 = lean_mk_string_unchecked("null", 4, 4);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_box(2);
lean_inc(x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_19);
x_28 = lean_array_push(x_27, x_24);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_box(3);
x_31 = l_Lean_Syntax_getArgs(x_2);
x_32 = l_Array_toSubarray___redArg(x_31, x_8, x_25);
x_33 = l_Array_ofSubarray___redArg(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_Lean_Syntax_getArg(x_2, x_25);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_1);
lean_ctor_set(x_38, 3, x_29);
lean_ctor_set(x_38, 4, x_6);
lean_ctor_set(x_38, 5, x_7);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_36);
lean_ctor_set(x_38, 8, x_37);
x_39 = lean_unbox(x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*9, x_39);
return x_38;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_isDefLike(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("Parser", 6, 6);
x_22 = lean_mk_string_unchecked("Command", 7, 7);
x_23 = lean_mk_string_unchecked("abbrev", 6, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
x_25 = lean_name_eq(x_2, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_mk_string_unchecked("definition", 10, 10);
x_27 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_26);
x_28 = lean_name_eq(x_2, x_27);
lean_dec(x_27);
x_3 = x_28;
goto block_19;
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_3 = x_25;
goto block_19;
}
block_19:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Command", 7, 7);
x_7 = lean_mk_string_unchecked("theorem", 7, 7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_name_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_mk_string_unchecked("opaque", 6, 6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_10);
x_12 = lean_name_eq(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_13);
x_15 = lean_name_eq(x_2, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("example", 7, 7);
x_17 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_16);
x_18 = lean_name_eq(x_2, x_17);
lean_dec(x_17);
lean_dec(x_2);
return x_18;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_isDefLike(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_2);
x_6 = l_Lean_Syntax_getKind(x_2);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Parser", 6, 6);
x_9 = lean_mk_string_unchecked("Command", 7, 7);
x_10 = lean_mk_string_unchecked("abbrev", 6, 6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = lean_name_eq(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_13);
x_15 = lean_name_eq(x_6, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_mk_string_unchecked("theorem", 7, 7);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_16);
x_18 = lean_name_eq(x_6, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_mk_string_unchecked("opaque", 6, 6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_19);
x_21 = lean_name_eq(x_6, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_22);
x_24 = lean_name_eq(x_6, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_mk_string_unchecked("example", 7, 7);
x_26 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_25);
x_27 = lean_name_eq(x_6, x_26);
lean_dec(x_26);
lean_dec(x_6);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_mk_string_unchecked("unexpected kind of definition", 29, 29);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_29, x_3, x_4, x_5);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_31 = l_Lean_Elab_Command_mkDefViewOfExample(x_1, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_33 = l_Lean_Elab_Command_mkDefViewOfInstance(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = l_Lean_Elab_Command_mkDefViewOfOpaque(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_35 = l_Lean_Elab_Command_mkDefViewOfTheorem(x_1, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_5);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_37 = l_Lean_Elab_Command_mkDefViewOfDef(x_1, x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_39 = l_Lean_Elab_Command_mkDefViewOfAbbrev(x_1, x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_5);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefView(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_2978_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("definition", 10, 10);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("Command", 7, 7);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = lean_mk_string_unchecked("DefView", 7, 7);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(2978u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_5);
x_25 = l_Lean_registerTraceClass(x_4, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_3017_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("instance", 8, 8);
x_4 = lean_mk_string_unchecked("mkInstanceName", 14, 14);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
lean_inc(x_2);
x_10 = l_Lean_Name_str___override(x_9, x_2);
x_11 = lean_mk_string_unchecked("Command", 7, 7);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("initFn", 6, 6);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = lean_mk_string_unchecked("_@", 2, 2);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = l_Lean_Name_str___override(x_16, x_8);
x_18 = l_Lean_Name_str___override(x_17, x_2);
x_19 = lean_mk_string_unchecked("DefView", 7, 7);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(3017u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_6);
x_26 = l_Lean_registerTraceClass(x_5, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclNameGen(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DefView(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclNameGen(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedDefKind = _init_l_Lean_Elab_instInhabitedDefKind();
l_Lean_Elab_instBEqDefKind = _init_l_Lean_Elab_instBEqDefKind();
lean_mark_persistent(l_Lean_Elab_instBEqDefKind);
l_Lean_Elab_instInhabitedDefViewElabHeaderData = _init_l_Lean_Elab_instInhabitedDefViewElabHeaderData();
lean_mark_persistent(l_Lean_Elab_instInhabitedDefViewElabHeaderData);
l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot = _init_l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot();
lean_mark_persistent(l_Lean_Elab_instToSnapshotTreeBodyProcessedSnapshot);
l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot = _init_l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot();
lean_mark_persistent(l_Lean_Elab_instToSnapshotTreeHeaderProcessedSnapshot);
l_Lean_Elab_instImpl____x40_Lean_Elab_DefView___hyg_597_ = _init_l_Lean_Elab_instImpl____x40_Lean_Elab_DefView___hyg_597_();
lean_mark_persistent(l_Lean_Elab_instImpl____x40_Lean_Elab_DefView___hyg_597_);
l_Lean_Elab_instTypeNameDefsParsedSnapshot = _init_l_Lean_Elab_instTypeNameDefsParsedSnapshot();
lean_mark_persistent(l_Lean_Elab_instTypeNameDefsParsedSnapshot);
l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot = _init_l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot();
lean_mark_persistent(l_Lean_Elab_instToSnapshotTreeDefsParsedSnapshot);
l_Lean_Elab_instInhabitedDefView = _init_l_Lean_Elab_instInhabitedDefView();
lean_mark_persistent(l_Lean_Elab_instInhabitedDefView);
if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_2978_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_3017_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
