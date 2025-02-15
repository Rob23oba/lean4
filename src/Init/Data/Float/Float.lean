/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Data.Int.Basic
import Init.Data.UInt.Lemmas
import Init.Data.ToString.Basic
import Init.Data.Float.Native

/-- Native floating point type, corresponding to the IEEE 754 *binary64* format
(`double` in C or `f64` in Rust). -/
structure Float where
  val : Quot (fun (a b : HardwareFloat) => a.isNaN ∧ b.isNaN)

instance : Nonempty Float := ⟨{ val := .mk _ ⟨0⟩ }⟩

def Float.isNaN (x : Float) : Bool :=
  x.val.lift (fun x' => x'.isNaN) (by
    intro a b ⟨ha, hb⟩
    dsimp
    rw [ha, hb]
  )

def Float.toHardwareFloat (x : Float) : HardwareFloat :=
  x.val.lift (fun val => if val.isNaN then ⟨0x7ff8_0000_0000_0000⟩ else val)
    (fun a b ⟨ha, hb⟩ => by simp only [ha, hb, ↓reduceIte])

def Float.ofHardwareFloat (x : HardwareFloat) : Float :=
  ⟨Quot.mk _ x⟩

@[extern "lean_float_add"]
def Float.add (x y : Float) : Float :=
  .ofHardwareFloat (x.toHardwareFloat + y.toHardwareFloat)

@[extern "lean_float_sub"]
def Float.sub (x y : Float) : Float :=
  .ofHardwareFloat (x.toHardwareFloat - y.toHardwareFloat)

@[extern "lean_float_mul"]
def Float.mul (x y : Float) : Float :=
  .ofHardwareFloat (x.toHardwareFloat * y.toHardwareFloat)

@[extern "lean_float_div"]
def Float.div (x y : Float) : Float :=
  .ofHardwareFloat (x.toHardwareFloat / y.toHardwareFloat)

@[extern "lean_float_negate"]
def Float.neg (x : Float) : Float :=
  .ofHardwareFloat (-x.toHardwareFloat)

def Float.lt (x y : Float) : Prop :=
  x.toHardwareFloat < y.toHardwareFloat

def Float.le (x y : Float) : Prop :=
  x.toHardwareFloat ≤ y.toHardwareFloat

/--
Raw transmutation from `UInt64`.

Floats and UInts have the same endianness on all supported platforms.
IEEE 754 very precisely specifies the bit layout of floats.
-/
@[extern "lean_float_of_bits"]
def Float.ofBits (x : UInt64) : Float :=
  .ofHardwareFloat ⟨x⟩

/--
Raw transmutation to `UInt64`.

Floats and UInts have the same endianness on all supported platforms.
IEEE 754 very precisely specifies the bit layout of floats.

Note that this function is distinct from `Float.toUInt64`, which attempts
to preserve the numeric value, and not the bitwise value.
-/
def Float.toBits (x : Float) : UInt64 :=
  x.toHardwareFloat.toBits

instance : Add Float := ⟨Float.add⟩
instance : Sub Float := ⟨Float.sub⟩
instance : Mul Float := ⟨Float.mul⟩
instance : Div Float := ⟨Float.div⟩
instance : Neg Float := ⟨Float.neg⟩
instance : LT Float  := ⟨Float.lt⟩
instance : LE Float  := ⟨Float.le⟩

/-- Note: this is not reflexive since `NaN != NaN`.-/
@[extern "lean_float_beq"] opaque Float.beq (a b : Float) : Bool

instance : BEq Float := ⟨Float.beq⟩

@[extern "lean_float_decLt"] opaque Float.decLt (a b : Float) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLt a b

@[extern "lean_float_decLe"] opaque Float.decLe (a b : Float) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLe a b

instance floatDecLt (a b : Float) : Decidable (a < b) := Float.decLt a b
instance floatDecLe (a b : Float) : Decidable (a ≤ b) := Float.decLe a b

@[extern "lean_float_to_string"] opaque Float.toString : Float → String
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt8` (including Inf), returns the maximum value of `UInt8`
(i.e. `UInt8.size - 1`).
-/
@[extern "lean_float_to_uint8"] opaque Float.toUInt8 : Float → UInt8
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt16` (including Inf), returns the maximum value of `UInt16`
(i.e. `UInt16.size - 1`).
-/
@[extern "lean_float_to_uint16"] opaque Float.toUInt16 : Float → UInt16
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt32` (including Inf), returns the maximum value of `UInt32`
(i.e. `UInt32.size - 1`).
-/
@[extern "lean_float_to_uint32"] opaque Float.toUInt32 : Float → UInt32
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt64` (including Inf), returns the maximum value of `UInt64`
(i.e. `UInt64.size - 1`).
-/
@[extern "lean_float_to_uint64"] opaque Float.toUInt64 : Float → UInt64
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `USize` (including Inf), returns the maximum value of `USize`
(i.e. `USize.size - 1`). This value is platform dependent).
-/
@[extern "lean_float_to_usize"] opaque Float.toUSize : Float → USize

@[extern "lean_float_isnan"] opaque Float.isNaN : Float → Bool
@[extern "lean_float_isfinite"] opaque Float.isFinite : Float → Bool
@[extern "lean_float_isinf"] opaque Float.isInf : Float → Bool
/-- Splits the given float `x` into a significand/exponent pair `(s, i)`
such that `x = s * 2^i` where `s ∈ (-1;-0.5] ∪ [0.5; 1)`.
Returns an undefined value if `x` is not finite.
-/
@[extern "lean_float_frexp"] opaque Float.frExp : Float → Float × Int

instance : ToString Float where
  toString := Float.toString

@[extern "lean_uint64_to_float"] opaque UInt64.toFloat (n : UInt64) : Float

instance : Inhabited Float where
  default := UInt64.toFloat 0

instance : Repr Float where
  reprPrec n prec := if n < UInt64.toFloat 0 then Repr.addAppParen (toString n) prec else toString n

instance : ReprAtom Float  := ⟨⟩

@[extern "sin"] opaque Float.sin : Float → Float
@[extern "cos"] opaque Float.cos : Float → Float
@[extern "tan"] opaque Float.tan : Float → Float
@[extern "asin"] opaque Float.asin : Float → Float
@[extern "acos"] opaque Float.acos : Float → Float
@[extern "atan"] opaque Float.atan : Float → Float
@[extern "atan2"] opaque Float.atan2 : Float → Float → Float
@[extern "sinh"] opaque Float.sinh : Float → Float
@[extern "cosh"] opaque Float.cosh : Float → Float
@[extern "tanh"] opaque Float.tanh : Float → Float
@[extern "asinh"] opaque Float.asinh : Float → Float
@[extern "acosh"] opaque Float.acosh : Float → Float
@[extern "atanh"] opaque Float.atanh : Float → Float
@[extern "exp"] opaque Float.exp : Float → Float
@[extern "exp2"] opaque Float.exp2 : Float → Float
@[extern "log"] opaque Float.log : Float → Float
@[extern "log2"] opaque Float.log2 : Float → Float
@[extern "log10"] opaque Float.log10 : Float → Float
@[extern "pow"] opaque Float.pow : Float → Float → Float
@[extern "sqrt"] opaque Float.sqrt : Float → Float
@[extern "cbrt"] opaque Float.cbrt : Float → Float
@[extern "ceil"] opaque Float.ceil : Float → Float
@[extern "floor"] opaque Float.floor : Float → Float
@[extern "round"] opaque Float.round : Float → Float
@[extern "fabs"] opaque Float.abs : Float → Float

instance : HomogeneousPow Float := ⟨Float.pow⟩

instance : Min Float := minOfLe

instance : Max Float := maxOfLe

/--
Efficiently computes `x * 2^i`.
-/
@[extern "lean_float_scaleb"]
opaque Float.scaleB (x : Float) (i : @& Int) : Float
