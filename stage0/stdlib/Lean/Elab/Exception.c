// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: Lean.InternalExceptionId Lean.Exception
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_43_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortCommandExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_103_(lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortTermExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_83_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortTacticException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_23_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_63_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_postponeExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_autoBoundImplicitExceptionId;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortTacticExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("postpone", 8, 8);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_registerInternalExceptionId(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_23_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("unsupportedSyntax", 17, 17);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_registerInternalExceptionId(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_43_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("abortCommandElab", 16, 16);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_registerInternalExceptionId(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_63_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("abortTermElab", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_registerInternalExceptionId(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_83_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("abortTactic", 11, 11);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_registerInternalExceptionId(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_103_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_mk_string_unchecked("autoBoundImplicit", 17, 17);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_registerInternalExceptionId(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_postponeExceptionId;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwPostpone___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwUnsupportedSyntax___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_string_unchecked("ill-formed syntax", 17, 17);
x_4 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_5 = l_Lean_throwError___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwIllFormedSyntax___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_Elab_autoBoundImplicitExceptionId;
x_4 = l_Lean_KVMap_empty;
x_5 = lean_mk_string_unchecked("localId", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lean_KVMap_insert(x_4, x_6, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_10, lean_box(0), x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_autoBoundImplicitExceptionId;
x_6 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_mk_string_unchecked("localId", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("x", 1, 1);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_KVMap_getName(x_4, x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_mk_string_unchecked("a universe level named '", 24, 24);
x_5 = l_Lean_stringToMessageData(x_4);
lean_dec(x_4);
x_6 = l_Lean_MessageData_ofName(x_3);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked("' has already been declared", 27, 27);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_throwError___redArg(x_1, x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Elab_abortCommandExceptionId;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwAbortCommand___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Elab_abortTermExceptionId;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwAbortTerm___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Elab_abortTacticExceptionId;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwAbortTactic___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortTacticException(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Elab_abortTacticExceptionId;
x_6 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isAbortTacticException(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortExceptionId(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_abortCommandExceptionId;
x_7 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Elab_abortTermExceptionId;
x_9 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_1, x_8);
x_2 = x_9;
goto block_5;
}
else
{
x_2 = x_7;
goto block_5;
}
block_5:
{
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_abortTacticExceptionId;
x_4 = l___private_Lean_InternalExceptionId_0__Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_26_(x_1, x_3);
return x_4;
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isAbortExceptionId(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
lean_inc(x_2);
x_7 = l_Lean_FileMap_toPosition(x_2, x_5);
x_8 = l_Lean_FileMap_toPosition(x_2, x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_box(0);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_3);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_4);
x_14 = lean_unbox(x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 2, x_14);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Elab_mkMessageCore(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_InternalExceptionId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_postponeExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_postponeExceptionId);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_23_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_unsupportedSyntaxExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_unsupportedSyntaxExceptionId);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_43_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortCommandExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortCommandExceptionId);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_63_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTermExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTermExceptionId);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_83_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTacticExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTacticExceptionId);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_103_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoBoundImplicitExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoBoundImplicitExceptionId);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
