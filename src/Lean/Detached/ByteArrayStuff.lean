prelude
import Init.Data.ByteArray

namespace ByteArray


-- the compiler should hopefully pick up on what we are doing here
def getUInt16LE (a : ByteArray) (i : Nat) (h : i + 2 ≤ a.size := by get_elem_tactic) : UInt16 :=
  let b1 := a[i]
  let b2 := a[i + 1]
  b1.toUInt16 ||| (b2.toUInt16 <<< 8)

def getUInt16BE (a : ByteArray) (i : Nat) (h : i + 2 ≤ a.size := by get_elem_tactic) : UInt16 :=
  let b1 := a[i]
  let b2 := a[i + 1]
  (b1.toUInt16 <<< 8) ||| b2.toUInt16

def getUInt32LE (a : ByteArray) (i : Nat) (h : i + 4 ≤ a.size := by get_elem_tactic) : UInt32 :=
  let b1 := a[i]
  let b2 := a[i + 1]
  let b3 := a[i + 2]
  let b4 := a[i + 3]
  b1.toUInt32 ||| (b2.toUInt32 <<< 8) ||| (b3.toUInt32 <<< 16) ||| (b4.toUInt32 <<< 24)

def getUInt32BE (a : ByteArray) (i : Nat) (h : i + 4 ≤ a.size := by get_elem_tactic) : UInt32 :=
  let b1 := a[i]
  let b2 := a[i + 1]
  let b3 := a[i + 2]
  let b4 := a[i + 3]
  (b1.toUInt32 <<< 24) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 8) ||| b4.toUInt32

unsafe def ugetUInt64BE (a : ByteArray) (i : USize) (h : i.toNat + 8 ≤ a.size := by get_elem_tactic) : UInt64 :=
  let b1 := a.uget i
  let b2 := a.uget (i + 1) lcProof
  let b3 := a.uget (i + 2) lcProof
  let b4 := a.uget (i + 3) lcProof
  let b5 := a.uget (i + 4) lcProof
  let b6 := a.uget (i + 5) lcProof
  let b7 := a.uget (i + 6) lcProof
  let b8 := a.uget (i + 7) lcProof
  (b1.toUInt64 <<< 56) ||| (b2.toUInt64 <<< 48) ||| (b3.toUInt64 <<< 40) ||| (b4.toUInt64 <<< 32) |||
    (b5.toUInt64 <<< 24) ||| (b6.toUInt64 <<< 16) ||| (b7.toUInt64 <<< 8) ||| b8.toUInt64

unsafe def ugetUInt64LE (a : ByteArray) (i : USize) : UInt64 :=
  let b1 := a.uget i lcProof
  let b2 := a.uget (i + 1) lcProof
  let b3 := a.uget (i + 2) lcProof
  let b4 := a.uget (i + 3) lcProof
  let b5 := a.uget (i + 4) lcProof
  let b6 := a.uget (i + 5) lcProof
  let b7 := a.uget (i + 6) lcProof
  let b8 := a.uget (i + 7) lcProof
  b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24) |||
    (b5.toUInt64 <<< 32) ||| (b6.toUInt64 <<< 40) ||| (b7.toUInt64 <<< 48) ||| (b8.toUInt64 <<< 56)

@[noinline]
unsafe def ugetUInt64LEHelper (a : ByteArray) (i : USize) (x : UInt8) : UInt64 :=
  ugetUInt64LE a i

unsafe def getUInt64LEImpl (a : ByteArray) (i : Nat) : UInt64 :=
  let x := a.get i lcProof
  ugetUInt64LEHelper a i.toUSize x

def getUInt64LE (a : ByteArray) (i : Nat) (h : i + 8 ≤ a.size := by get_elem_tactic) : UInt64 :=
  let b1 := a[i]
  let b2 := a[i + 1]
  let b3 := a[i + 2]
  let b4 := a[i + 3]
  let b5 := a[i + 4]
  let b6 := a[i + 5]
  let b7 := a[i + 6]
  let b8 := a[i + 7]
  b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24) |||
    (b5.toUInt64 <<< 32) ||| (b6.toUInt64 <<< 40) ||| (b7.toUInt64 <<< 48) ||| (b8.toUInt64 <<< 56)


def getUInt64BE (a : ByteArray) (i : Nat) (h : i + 8 ≤ a.size := by get_elem_tactic) : UInt64 :=
  let b1 := a[i]
  let b2 := a[i + 1]
  let b3 := a[i + 2]
  let b4 := a[i + 3]
  let b5 := a[i + 4]
  let b6 := a[i + 5]
  let b7 := a[i + 6]
  let b8 := a[i + 7]
  (b1.toUInt64 <<< 56) ||| (b2.toUInt64 <<< 48) ||| (b3.toUInt64 <<< 40) ||| (b4.toUInt64 <<< 32) |||
    (b5.toUInt64 <<< 24) ||| (b6.toUInt64 <<< 16) ||| (b7.toUInt64 <<< 8) ||| b8.toUInt64

end ByteArray
