/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Markus Himmel
-/
prelude
import Lean.Meta.LitValues
import Init.Data.SInt.Lemmas
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Int

open Lean Meta Simp

macro "declare_sint_simprocs" typeName:ident : command =>
let ofNat := typeName.getId ++ `ofNat
let ofInt := typeName.getId ++ `ofInt
let ofIntLE := mkIdent (typeName.getId ++ `ofIntLE)
let toInt := mkIdent (typeName.getId ++ `toInt)
let toNatClampNeg := mkIdent (typeName.getId ++ `toNatClampNeg)
let fromExpr := mkIdent `fromExpr
`(
namespace $typeName

def $fromExpr (e : Expr) : SimpM (Option $typeName) := do
  if let some (n, _) ← getOfNatValue? e $(quote typeName.getId) then
    return some ($(mkIdent ofNat) n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a $(quote typeName.getId) | return none
  return some ($(mkIdent ofInt) (- n))

@[inline] def reduceUnary (declName : Name) (arity : Nat) (op : $typeName → $typeName) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : $typeName → $typeName → $typeName) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

builtin_dsimproc [simp, seval] $(mkIdent `reduceNeg):ident ((- _ : $typeName)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← ($fromExpr arg) | return .continue
    return .done <| toExpr (- v)

builtin_dsimproc [simp, seval] $(mkIdent `reduceAdd):ident ((_ + _ : $typeName)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceMul):ident ((_ * _ : $typeName)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceSub):ident ((_ - _ : $typeName)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceDiv):ident ((_ / _ : $typeName)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceMod):ident ((_ % _ : $typeName)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_dsimproc [simp, seval] $(mkIdent `reduceAnd):ident ((_ &&& _ : $typeName)) := reduceBin ``HAnd.hAnd 6 (· &&& ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceOr):ident ((_ ||| _ : $typeName)) := reduceBin ``HOr.hOr 6 (· ||| ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceXor):ident ((_ ^^^ _ : $typeName)) := reduceBin ``HXor.hXor 6 (· ^^^ ·)

builtin_dsimproc [simp, seval] $(mkIdent `reduceShiftLeft):ident ((_ <<< _ : $typeName)) := reduceBin ``HShiftLeft.hShiftLeft 6 (· <<< ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceShiftRight):ident ((_ >>> _ : $typeName)) := reduceBin ``HShiftRight.hShiftRight 6 (· >>> ·)

builtin_dsimproc [simp, seval] $(mkIdent `reduceComplement):ident ((~~~ _ : $typeName)) := reduceUnary ``Complement.complement 6 (~~~ ·)

builtin_simproc [simp, seval] $(mkIdent `reduceLT):ident  (( _ : $typeName) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] $(mkIdent `reduceLE):ident  (( _ : $typeName) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] $(mkIdent `reduceGT):ident  (( _ : $typeName) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] $(mkIdent `reduceGE):ident  (( _ : $typeName) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] $(mkIdent `reduceEq):ident  (( _ : $typeName) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] $(mkIdent `reduceNe):ident  (( _ : $typeName) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] $(mkIdent `reduceBEq):ident  (( _ : $typeName) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] $(mkIdent `reduceBNe):ident  (( _ : $typeName) != _)  := reduceBoolPred ``bne 4 (. != .)

builtin_dsimproc [simp, seval] $(mkIdent `reduceOfIntLE):ident ($ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity $(quote ofIntLE.getId) 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := $(mkIdent ofInt) value
  return .done <| toExpr value

builtin_dsimproc [simp, seval] $(mkIdent `reduceOfNat):ident ($(mkIdent ofNat) _) := fun e => do
  unless e.isAppOfArity $(quote ofNat) 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := $(mkIdent ofNat) value
  return .done <| toExpr value

builtin_dsimproc [simp, seval] $(mkIdent `reduceOfInt):ident ($(mkIdent ofInt) _) := fun e => do
  unless e.isAppOfArity $(quote ofInt) 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := $(mkIdent ofInt) value
  return .done <| toExpr value

builtin_dsimproc [simp, seval] $(mkIdent `reduceToInt):ident ($toInt _) := fun e => do
  unless e.isAppOfArity $(quote toInt.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toInt v
  return .done <| toExpr n

builtin_dsimproc [simp, seval] $(mkIdent `reduceToNatClampNeg):ident ($toNatClampNeg _) := fun e => do
  unless e.isAppOfArity $(quote toNatClampNeg.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for Int values. We don't want to unfold in the symbolic evaluator. -/
builtin_dsimproc [seval] isValue ((OfNat.ofNat _ : $typeName)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end $typeName
)

declare_sint_simprocs Int8
declare_sint_simprocs Int16
declare_sint_simprocs Int32
declare_sint_simprocs Int64

/-
We do not use the normal simprocs for `ISize` since the result of most operations depend on an opaque value: `System.Platform.numBits`.
However, we do reduce natural literals using the fact this opaque value is at least `32`.
-/
namespace ISize

builtin_simproc [simp, seval] reduceToNatClampNeg (ISize.toNatClampNeg _) := fun e => do
  let_expr ISize.toNatClampNeg e ← e | return .continue
  if let some (n, _) ← getOfNatValue? e ``ISize then
    unless n < 2 ^ 31 do return .continue
    let e := toExpr n
    let p ← mkDecideProof (← mkLT e (mkNatLit (2 ^ 31)))
    let p := mkApp2 (mkConst ``ISize.toNatClampNeg_ofNat_of_lt) e p
    return .done { expr := e, proof? := p }

  let_expr Neg.neg _ _ a ← e | return .continue
  let some (n, _) ← getOfNatValue? a ``ISize | return .continue
  unless n ≤ 2 ^ 31 do return .continue
  let e := toExpr n
  let p ← mkDecideProof (← mkLE e (mkNatLit (2 ^ 31)))
  let p := mkApp2 (mkConst ``ISize.toNatClampNeg_neg_ofNat_of_le) e p
  return .done { expr := toExpr 0, proof? := p }

builtin_simproc [simp, seval] reduceToInt (ISize.toInt _) := fun e => do
  let_expr ISize.toInt e ← e | return .continue
  if let some (n, _) ← getOfNatValue? e ``ISize then
    unless n < 2 ^ 31 do return .continue
    let e := toExpr n
    let p ← mkDecideProof (← mkLT e (mkNatLit (2 ^ 31)))
    let p := mkApp2 (mkConst ``ISize.toInt_ofNat_of_lt) e p
    return .done { expr := toExpr (n : Int), proof? := p }

  let_expr Neg.neg _ _ a ← e | return .continue
  let some (n, _) ← getOfNatValue? a ``ISize | return .continue
  unless n ≤ 2 ^ 31 do return .continue
  let e := toExpr n
  let p ← mkDecideProof (← mkLE e (mkNatLit (2 ^ 31)))
  let p := mkApp2 (mkConst ``ISize.toInt_neg_ofNat_of_le) e p
  return .done { expr := toExpr (-n : Int), proof? := p }

/--
Reduce a predicate (`<`, `≤`, `=`, `≠`) by trying to convert both sides into an `Int`
using `reduceToInt` and using the helper lemma `lemma` of the form
`x.toInt r y.toInt ↔ x r y` (inv = false) or `x r y ↔ x.toInt r y.toInt` (inv = true).

-/
private def reduceBinPredToInt (declName : Name) (arity : Nat) (op : Int → Int → Bool)
    (lemma : Name) (inv : Bool) (intPred : Expr) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let toIntLhs : Expr := .app (mkConst ``ISize.toInt) e.appFn!.appArg!
  let toIntRhs : Expr := .app (mkConst ``ISize.toInt) e.appArg!
  let .done { expr := lhs, proof? := some hlhs } ← reduceToInt toIntLhs | return .continue
  let .done { expr := rhs, proof? := some hrhs } ← reduceToInt toIntRhs | return .continue
  let some lhsValue ← Int.fromExpr? lhs | return .continue
  let some rhsValue ← Int.fromExpr? rhs | return .continue
  let toIntRel := mkApp2 intPred toIntLhs toIntRhs
  let intRel := mkApp2 intPred lhs rhs
  let .done { expr := result, proof? := some hresult } ←
    evalPropStep intRel (op lhsValue rhsValue) | return .continue
  let intToProp ← mkArrow Int.mkType (.sort 0)
  let lemmaExpr := mkApp2 (mkConst lemma) e.appFn!.appArg! e.appArg!
  let lemmaExpr := if inv then mkApp3 (mkConst ``Iff.symm) intRel e lemmaExpr else lemmaExpr
  let propext := mkApp3 (mkConst ``propext) e toIntRel lemmaExpr
  let congrArg := mkApp6 (mkConst ``congrArg [1, 1]) Int.mkType intToProp toIntLhs lhs intPred hlhs
  let congr := mkApp8 (mkConst ``congr [1, 1]) Int.mkType (.sort 0)
    (.app intPred toIntLhs) (.app intPred lhs) toIntRhs rhs congrArg hrhs
  let trans1 := mkApp6 (mkConst ``Eq.trans [1]) (.sort 0) e toIntRel intRel propext congr
  let proof := mkApp6 (mkConst ``Eq.trans [1]) (.sort 0) e intRel result trans1 hresult
  logInfo m!"the proof {proof}"
  return .done { expr := result, proof? := proof }

def theex (r : ISize → ISize → Prop) (r' : Int → Int → Prop) (x y : ISize)
    (hlhs : x.toInt = lhsValue) (hrhs : y.toInt = rhsValue)
    (hresult : r' lhsValue rhsValue = result)
    (lemma : r x y ↔ r' x.toInt y.toInt) : r x y = result := by
  exact ((propext lemma).trans (congr (congrArg r' hlhs) hrhs)).trans hresult

#print theex

simproc [simp, seval] reduceEq ((_ : ISize) = _) :=
  reduceBinPredToInt ``Eq 3 (· = ·) ``toInt_inj true
    (.app (mkConst ``Eq [1]) Int.mkType)

simproc [simp, seval] reduceLT ((_ : ISize) < _) :=
  reduceBinPredToInt ``LT.lt 4 (· < ·) ``lt_iff_toInt_lt false
    (mkApp2 (mkConst ``LT.lt [1]) Int.mkType Int.mkInstLT)

simproc [simp, seval] reduceLE ((_ : ISize) ≤ _) :=
  reduceBinPredToInt ``LE.le 4 (· ≤ ·) ``le_iff_toInt_le false
    (mkApp2 (mkConst ``LE.le [1]) Int.mkType Int.mkInstLE)
