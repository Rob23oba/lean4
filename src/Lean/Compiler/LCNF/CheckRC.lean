/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Lean.Compiler.LCNF.PrettyPrinter
public import Lean.Compiler.LCNF.CompatibleTypes

public section

namespace Lean.Compiler.LCNF

namespace Check
namespace Impure

open ImpureType

structure VarRCInfo where
  rc : Nat
  borrowed : Bool := false
  parents : Array FVarId := #[]
  children : Array FVarId := #[]

def deadInfo : VarRCInfo where
  rc := 0
  borrowed := false
  parents := #[]
  children := #[]

structure State where
  rc : FVarIdMap VarRCInfo := {}
  subst : FVarSubst .impure := {}

abbrev M := StateRefT State CompilerM

def isDead (v : FVarId) : M Bool := do
  let some info := (← get).rc.get? v | return false
  return !info.borrowed && info.rc = 0

partial def maybeKill (v : FVarId) : M Unit := do
  let some info := (← get).rc.get? v | pure ()
  if ← pure info.borrowed <&&> info.parents.anyM isDead then
    modify fun state => { state with rc := state.rc.insert v deadInfo }
    for child in info.children do
      maybeKill child

def kill (v : FVarId) : M Unit := do
  let .fvar v := (← get).subst.getD v (.fvar v) |
    throwError "Can't delete an erased value"
  let some info := (← get).rc.get? v |
    throwError "Can't delete a scalar value"
  if info.borrowed then
    throwError "Can't delete a borrowed value"
  modify fun state => { state with rc := state.rc.insert v deadInfo }
  for child in info.children do
    maybeKill child

def makeScalar (v : FVarId) : M Unit := do
  let .fvar v := (← get).subst.getD v (.fvar v) | pure ()
  modify fun state => { state with rc := state.rc.erase v }

def consume (v : FVarId) (n : Nat := 1) : M Unit := do
  let .fvar v := (← get).subst.getD v (.fvar v) | pure ()
  let some info := (← get).rc.get? v | pure ()
  if info.rc < n then
    if !info.borrowed && info.rc = 0 then
      throwError "Failed to consume {← getBinderName v} {n} times, potential use after free"
    throwError "Failed to consume {← getBinderName v} {n} times, only {info.rc} reference count available"
  modify fun state => { state with
    rc := state.rc.modify v fun entry => { entry with rc := entry.rc - n } }
  maybeKill v

def useVar (v : FVarId) : M Unit := do
  let .fvar v := (← get).subst.getD v (.fvar v) | pure ()
  if ← isDead v then
    throwError "Can't use {← getBinderName v}, potential use after free"

def checkShared (v : FVarId) : M Unit := do
  let .fvar v := (← get).subst.getD v (.fvar v) | pure ()
  let some info := (← get).rc.get? v | pure ()
  if info.borrowed then
    throwError "Can't write into borrowed value {← getBinderName v}"
  if info.rc = 0 then
    throwError "Can't write into {← getBinderName v}, potential use after free"
  if info.rc > 1 then
    throwError "Can't write into {← getBinderName v}, variable has a reference count of at least \
      {info.rc}"

def inc (v : FVarId) (n : Nat := 1) : M Unit := do
  let .fvar v := (← get).subst.getD v (.fvar v) | pure ()
  let some info := (← get).rc.get? v | pure ()
  if !info.borrowed && info.rc == 0 then
    throwError "Can't increment {← getBinderName v}, potential use after free"
  modify fun state => { state with
    rc := state.rc.modify v fun entry => { entry with rc := entry.rc + n } }

def consumeArg (v : Arg .impure) : M Unit := do
  match v with
  | .erased => pure ()
  | .fvar f => consume f

def useArg (v : Arg .impure) : M Unit := do
  match v with
  | .erased => pure ()
  | .fvar f => useVar f

def checkLeaks : M Unit := do
  let map : Std.TreeMap FVarId _ _ := (← get).rc
  for (var, info) in map do
    if info.rc > 0 then
      throwError "Detected RC leak: {← getBinderName var} still has an RC of at least {info.rc} upon return"

def addOwned (v : FVarId) : M Unit := do
  modify fun state => { state with rc := state.rc.insert v { rc := 1 } }

def addChild (parent child : FVarId) : M Unit := do
  modify fun state => { state with rc := state.rc.modify parent fun info =>
    { info with children := info.children.push child } }

def addBorrowed (v : FVarId) (parents : Array (Arg .impure)) : M Unit := do
  let parents := parents.filterMap fun | .erased => none | .fvar f => some f
  modify fun state => { state with rc := state.rc.insert v { rc := 0, borrowed := true, parents } }
  for parent in parents do
    addChild parent v

def checkLetDecl (decl : LetDecl .impure) : M Unit := do
  match decl.value with
  | .fvar var args | .reuse var _ _ args =>
    consume var; args.forM consumeArg; addOwned decl.fvarId
  | .pap _ args => args.forM consumeArg; addOwned decl.fvarId
  | .fap nm args =>
    let some sig ← getImpureSignature? nm | throwError "Can't find impure signature for {nm}"
    if args.size != sig.params.size then
      throwError "Argument count mismatch for {nm}: expected {sig.params.size} arguments but \
        got {args.size}"
    for p in sig.params, a in args do
      unless p.borrow do
        consumeArg a
    for p in sig.params, a in args do
      if p.borrow then
        useArg a
    if nm == ``Array.getInternalBorrowed then
      addBorrowed decl.fvarId #[args[1]!]
    else if nm == ``Array.get!InternalBorrowed then
      addBorrowed decl.fvarId #[args[1]!, args[2]!]
    else if nm == ``Array.ugetBorrowed then
      addBorrowed decl.fvarId #[args[1]!]
    else if decl.type.isPossibleRef then
      addOwned decl.fvarId
  | .ctor info args => args.forM consumeArg; if info.isRef then addOwned decl.fvarId
  | .box _ty v => consume v; if decl.type.isPossibleRef then addOwned decl.fvarId
  | .reset _ f => consume f; addOwned decl.fvarId
  | .erased => pure ()
  | .lit _ => if decl.type.isPossibleRef then addOwned decl.fvarId
  | .isShared v => useVar v
  | .sproj _ _ f => useVar f
  | .uproj _ f => useVar f
  | .oproj _ f => useVar f; addBorrowed decl.fvarId #[.fvar f]
  | .unbox v => useVar v

partial def check (c : Code .impure) : M Unit := do
  match c with
  | .let decl k =>
    checkLetDecl decl
    modifyLCtx fun lctx => lctx.addLetDecl decl
    check k
  | .jp decl k =>
    modifyLCtx fun lctx => lctx.addFunDecl decl
    check k
  | .unreach _ => return
  | .return v => consume v; checkLeaks
  | .dec f n _ _ k => consume f n; check k
  | .inc f n _ _ k => inc f n; check k
  | .del f k => kill f; check k
  | .setTag f _ k => checkShared f; check k
  | .oset f _ arg k => checkShared f; useArg arg; check k
  | .sset f _ _ _ _ k => checkShared f; check k
  | .uset f _ _ k => checkShared f; check k
  | .cases c =>
    let lctx := (← getThe CompilerM.State).lctx
    let state ← get
    useVar c.discr
    for alt in c.alts do
      modifyLCtx fun _ => lctx
      set state
      match alt with
      | .ctorAlt info k =>
        if info.isScalar then
          makeScalar c.discr
        check k
      | .default k => check k
  | .jmp jp args =>
    let decl ← getFunDecl jp
    if args.size != decl.params.size then
      throwError "Join point argument count mismatch: expected {decl.params.size} arguments but \
        got {args.size}"
    for param in decl.params, arg in args do
      let substArg ← match arg with
        | .erased => pure arg
        | .fvar v => pure <| (← get).subst.getD v (.fvar v)
      modify fun state => { state with subst := state.subst.insert param.fvarId substArg }
    check decl.value

end Impure
end Check

def Decl.checkRC (decl : Decl .impure) : CompilerM Unit :=
  decl.value.forCodeM fun code => (Check.Impure.check code).run' {}

end Lean.Compiler.LCNF
