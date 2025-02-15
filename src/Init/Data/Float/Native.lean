/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Data.Int.Basic
import Init.Data.ToString.Basic
import Init.Data.UInt.Basic

structure FloatSpec where
  float : Type
  val   : float
  lt    : float → float → Prop
  le    : float → float → Prop
  decLt : DecidableRel lt
  decLe : DecidableRel le

-- Just show FloatSpec is inhabited.
opaque floatSpec : FloatSpec := {
  float := Unit,
  val   := (),
  lt    := fun _ _ => True,
  le    := fun _ _ => True,
  decLt := fun _ _ => inferInstanceAs (Decidable True),
  decLe := fun _ _ => inferInstanceAs (Decidable True)
}

/-- Native floating point type, corresponding to the IEEE 754 *binary64* format
(`double` in C or `f64` in Rust). -/
structure HardwareFloat where
  /--
  Raw transmutation from `UInt64`.

  Floats and UInts have the same endianness on all supported platforms.
  IEEE 754 very precisely specifies the bit layout of floats.
  -/
  ofBits ::
  /--
  Raw transmutation to `UInt64`.

  Floats and UInts have the same endianness on all supported platforms.
  IEEE 754 very precisely specifies the bit layout of floats.

  Note that this function is distinct from `Float.toUInt64`, which attempts
  to preserve the numeric value, and not the bitwise value.
  -/
  toBits : UInt64

attribute [extern "lean_float_of_bits"] HardwareFloat.ofBits
attribute [extern "lean_float_to_bits"] HardwareFloat.toBits

instance : Inhabited HardwareFloat := ⟨.ofBits 0⟩

/--
Returns whether the sign bit of a floating point value is set,
i.e. the value is negative or -0 or a nan value with sign bit set.
-/
@[inline]
def HardwareFloat.signBit (x : HardwareFloat) : Bool :=
  x.toBits >>> 63 != 0

/--
Returns the exponent part of the bitwise representation of the floating point
number (1023 means 2^0, 2047 means nan or infinity).
-/
@[inline]
def HardwareFloat.exponentPart (x : HardwareFloat) : UInt64 :=
  (x.toBits >>> 52) &&& 0x7FF

/--
Returns the mantissa of the given floating point value.
-/
@[inline]
def HardwareFloat.mantissa (x : HardwareFloat) : UInt64 :=
  x.toBits &&& 0x000F_FFFF_FFFF_FFFF

/--
Converts the parts of a floating point number to a floating point number.
In particular, `Float.fromParts x.signBit x.exponentPart x.mantissa = x`.
This function assumes that `exp < 2048` and `mantissa < 2 ^ 52`.
-/
def HardwareFloat.fromParts (sign : Bool) (exp : UInt64) (mantissa : UInt64) : HardwareFloat :=
  let bits := (exp <<< 52) ||| mantissa
  ⟨if sign then bits ||| 0x8000_0000_0000_0000 else bits⟩

/-- Note: this is not reflexive since `NaN != NaN`.-/
@[extern "lean_float_beq"]
def HardwareFloat.beq (a b : HardwareFloat) : Bool :=
  if a.exponentPart == 0x7ff && a.mantissa != 0 then false -- a is nan
  else if b.exponentPart == 0x7ff && b.mantissa != 0 then false -- b is nan
  else if a.toBits &&& 0x7fff_ffff_ffff_ffff == 0
    && b.toBits &&& 0x7fff_ffff_ffff_ffff == 0 then true -- a and b are +/- 0
  else a.toBits == b.toBits

instance : BEq HardwareFloat := ⟨HardwareFloat.beq⟩

@[extern "lean_float_isnan"]
def HardwareFloat.isNaN (x : HardwareFloat) : Bool :=
  x != x

@[extern "lean_float_isfinite"]
def HardwareFloat.isFinite (x : HardwareFloat) : Bool :=
  x.exponentPart != 0x7ff

@[extern "lean_float_isinf"]
def HardwareFloat.isInf (x : HardwareFloat) : Bool :=
  x.exponentPart == 0x7ff && x.mantissa == 0

@[extern "lean_float_decLt"]
def HardwareFloat.blt (x y : HardwareFloat) : Bool :=
  if x.isNaN || y.isNaN then false
  else if x == ⟨0⟩ && y == ⟨0⟩ then false -- a and b are +/- 0
  else
    match x.signBit, y.signBit with
    | false, false => x.toBits < y.toBits -- positive < positive
    | false, true => false                -- positive < negative
    | true, false => true                 -- negative < positive
    | true, true => y.toBits < x.toBits   -- negative < negative

@[extern "lean_float_decLe"]
def HardwareFloat.ble (x y : HardwareFloat) :=
  x.blt y || x == y

def HardwareFloat.lt (x y : HardwareFloat) : Prop :=
  HardwareFloat.blt x y

def HardwareFloat.le (x y : HardwareFloat) : Prop :=
  HardwareFloat.ble x y

def HardwareFloat.toRatParts (x : HardwareFloat) : Int × Nat :=
  let sign : Int := if x.signBit then -1 else 1
  if x.exponentPart == 0 then
    (x.mantissa.toNat * sign, 1 <<< (1023 + 52 - 1)) -- subnormal
  else if x.exponentPart < 1023 + 52 then
    ((x.mantissa.toNat + 0x0010_0000_0000_0000) * sign,
      1 <<< (1023 + 52 - x.exponentPart.toNat))
  else
    (((x.mantissa.toNat + 0x0010_0000_0000_0000)
      <<< (x.exponentPart.toNat - (1023 + 52))) * sign, 1) -- integer

/--
Returns `log 2 (x / y)`, i.e. a value `z` such that
`2 ^ z * y ≤ x` and `x < 2 ^ (z + 1) * y`.
Assumes that `x` and `y` are not zero.
Internally used to define floating point operations.
-/
def Nat.log2Div (x y : Nat) : Int :=
  let approx : Int := x.log2 - y.log2
  -- check if approximation was too high
  --     x < 2 ^ (x.log2 - y.log2) * y
  -- <-> x * 2 ^ y.log2 < y * 2 ^ x.log2
  if x <<< y.log2 < y <<< x.log2 then approx - 1 else approx

/--
Returns `x / y`, rounded to the nearest integer.
If two integers are equally far apart from `x / y`, then return the even one.
Assumes that `y` isn't zero.
Internally used to define floating point operations.
-/
def Nat.roundDivToEven (x y : Nat) : Nat :=
  let div := 2 * x / y
  if div % 4 == 1 && div * y = 2 * x then
    div / 2
  else
    (div + 1) / 2

def HardwareFloat.fromRatParts (sign : Bool) (x y : Nat) : HardwareFloat :=
  if x == 0 then HardwareFloat.fromParts sign 0 0 else
  let exp := x.log2Div y
  if exp < -1022 then
    -- subnormal
    let mantissa := Nat.roundDivToEven (x <<< (1022 + 52)) y
    if mantissa == 0x0010_0000_0000_0000 then -- overflow
      HardwareFloat.fromParts sign 1 0 -- smallest normal number
    else
      HardwareFloat.fromParts sign 0 mantissa.toUInt64
  else if exp < 1024 then
    -- normal
    let mantissa := Nat.roundDivToEven (x <<< (52 - exp).toNat) (y <<< (exp - 52).toNat)
    if mantissa == 0x0020_0000_0000_0000 then -- overflow
      HardwareFloat.fromParts sign (exp + 1024).natAbs.toUInt64 0
    else
      HardwareFloat.fromParts sign (exp + 1023).natAbs.toUInt64
        (mantissa.toUInt64 &&& 0x000f_ffff_ffff_ffff)
  else
    -- infinity
    HardwareFloat.fromParts sign 2047 0

/--
Returns an opaque nan value. Because we can't guarantee that this function actually
returns a nan value, `HardwareFloat.makeNan` is instead used in practice.
-/
private opaque HardwareFloat.opaqueMakeNanBits (decl : Lean.Name) (x y : HardwareFloat) : UInt64 :=
  0x7ff8000000000000 -- we just define this to make the following functions computable

/--
Returns true if the given float is a nan value and not one of the canonical nan values.
This function is mainly used to implement `Float.makeNan`.
-/
def HardwareFloat.isNonCanonicalNan (x : HardwareFloat) : Bool :=
  let bits := x.toBits
  bits &&& 0x7ff0_0000_0000_0000 == 0x7ff0_0000_0000_0000 &&
    x.mantissa != 0x0008_0000_0000_0000

/--
Auxiliary function to define the opaque nan behavior of the float functions.
-/
def HardwareFloat.makeNan (decl : Lean.Name) (x y : HardwareFloat) : HardwareFloat :=
  if !x.isNonCanonicalNan && !y.isNonCanonicalNan then
    -- if both values are either canonical nans or not nans, return a canonical nan
    -- sign stays opaque
    ⟨(HardwareFloat.opaqueMakeNanBits decl x y &&& 0x8000_0000_0000_0000)
      ||| 0x7ff8_0000_0000_0000⟩
  else
    -- otherwise return any arithmetic nan value
    ⟨HardwareFloat.opaqueMakeNanBits decl x y ||| 0x7ff8_0000_0000_0000⟩

@[extern "lean_float_negate"] def HardwareFloat.neg (x : HardwareFloat) : HardwareFloat :=
  ⟨x.toBits ^^^ 0x8000_0000_0000_0000⟩ -- flip the sign bit

@[extern "lean_float_add"]
def HardwareFloat.add (x y : HardwareFloat) : HardwareFloat :=
  if x.isNaN || y.isNaN then HardwareFloat.makeNan `add x y
  else if x.isInf then
    if y.isInf && (x.signBit != y.signBit) then HardwareFloat.makeNan `add x y
    else x
  else if y.isInf then y
  -- special case -0 + -0 = -0
  else if x.toBits == 0x8000_0000_0000_0000 && y.toBits == 0x8000_0000_0000_0000 then x
  else
    let (a₁, b₁) := x.toRatParts
    let (a₂, b₂) := y.toRatParts
    -- naive rational number addition
    let a := a₁ * b₂ + a₂ * b₁
    let b := b₁ * b₂
    HardwareFloat.fromRatParts (a < 0) a.natAbs b

@[extern "lean_float_sub"]
def HardwareFloat.sub (x y : HardwareFloat) : HardwareFloat :=
  x.add y.neg

@[extern "lean_float_mul"]
def HardwareFloat.mul (x y : HardwareFloat) : HardwareFloat :=
  if x.isNaN || y.isNaN then HardwareFloat.makeNan `Float.mul x y
  else if x.isInf then
    if y == ⟨0⟩ then HardwareFloat.makeNan `Float.mul x y
    else HardwareFloat.fromParts (x.signBit ^^ y.signBit) 2047 0
  else if y.isInf then
    if x == ⟨0⟩ then HardwareFloat.makeNan `Float.mul x y
    else HardwareFloat.fromParts (x.signBit ^^ y.signBit) 2047 0
  else
    let (a₁, b₁) := x.toRatParts
    let (a₂, b₂) := y.toRatParts
    let a := a₁ * a₂
    let b := b₁ * b₂
    HardwareFloat.fromRatParts (x.signBit ^^ y.signBit) a.natAbs b

@[extern "lean_float_div"]
def HardwareFloat.div (x y : HardwareFloat) : HardwareFloat :=
  if x.isNaN || y.isNaN then HardwareFloat.makeNan `Float.div x y
  else if x.isInf then
    if y.isInf then HardwareFloat.makeNan `Float.div x y
    else HardwareFloat.fromParts (x.signBit ^^ y.signBit) 2047 0
  else if y.isInf then HardwareFloat.fromParts (x.signBit ^^ y.signBit) 0 0
  else if y == ⟨0⟩ then
    if x == ⟨0⟩ then HardwareFloat.makeNan `Float.div x y
    else HardwareFloat.fromParts (x.signBit ^^ y.signBit) 2047 0
  else
    let (a₁, b₁) := x.toRatParts
    let (a₂, b₂) := y.toRatParts
    let a := a₁ * b₂
    let b := b₁ * a₂
    HardwareFloat.fromRatParts (x.signBit ^^ y.signBit) a.natAbs b.natAbs

instance : Add HardwareFloat := ⟨HardwareFloat.add⟩
instance : Sub HardwareFloat := ⟨HardwareFloat.sub⟩
instance : Mul HardwareFloat := ⟨HardwareFloat.mul⟩
instance : Div HardwareFloat := ⟨HardwareFloat.div⟩
instance : Neg HardwareFloat := ⟨HardwareFloat.neg⟩
instance : LT HardwareFloat  := ⟨HardwareFloat.lt⟩
instance : LE HardwareFloat  := ⟨HardwareFloat.le⟩

@[extern "lean_float_decLt"]
instance HardwareFloat.decLt (a b : HardwareFloat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (_ = true))

@[extern "lean_float_decLe"]
instance HardwareFloat.decLe (a b : HardwareFloat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (_ = true))

@[extern "lean_float_to_string"] opaque HardwareFloat.toString : HardwareFloat → String

/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt8` (including Inf), returns the maximum value of `UInt8`
(i.e. `UInt8.size - 1`).
-/
@[extern "lean_float_to_uint8"]
def HardwareFloat.toUInt8 (x : HardwareFloat) : UInt8 :=
  if x.isNaN || x < ⟨0⟩ then 0
  else
    let (a, b) := x.toRatParts
    if a / b < UInt8.size then (a / b).toNat.toUInt8 else (UInt8.size - 1).toUInt8

/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt16` (including Inf), returns the maximum value of `UInt16`
(i.e. `UInt16.size - 1`).
-/
@[extern "lean_float_to_uint16"]
def HardwareFloat.toUInt16 (x : HardwareFloat) : UInt16 :=
  if x.isNaN || x < ⟨0⟩ then 0
  else
    let (a, b) := x.toRatParts
    if a / b < UInt16.size then (a / b).toNat.toUInt16 else (UInt8.size - 1).toUInt16

/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt32` (including Inf), returns the maximum value of `UInt32`
(i.e. `UInt32.size - 1`).
-/
@[extern "lean_float_to_uint32"]
def HardwareFloat.toUInt32 (x : HardwareFloat) : UInt32 :=
  if x.isNaN || x < ⟨0⟩ then 0
  else
    let (a, b) := x.toRatParts
    if a / b < UInt32.size then (a / b).toNat.toUInt32 else (UInt8.size - 1).toUInt32

/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt64` (including Inf), returns the maximum value of `UInt64`
(i.e. `UInt64.size - 1`).
-/
@[extern "lean_float_to_uint64"]
def HardwareFloat.toUInt64 (x : HardwareFloat) : UInt64 :=
  if x.isNaN || x < ⟨0⟩ then 0
  else
    let (a, b) := x.toRatParts
    if a / b < UInt64.size then (a / b).toNat.toUInt64 else (UInt8.size - 1).toUInt64

/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `USize` (including Inf), returns the maximum value of `USize`
(i.e. `USize.size - 1`). This value is platform dependent).
-/
@[extern "lean_float_to_usize"]
def HardwareFloat.toUSize (x : HardwareFloat) : USize :=
  if x.isNaN || x < ⟨0⟩ then 0
  else
    let (a, b) := x.toRatParts
    if a / b < USize.size then (a / b).toNat.toUSize else (USize.size - 1).toUSize

/-- Splits the given float `x` into a significand/exponent pair `(s, i)`
such that `x = s * 2^i` where `s ∈ (-1;-0.5] ∪ [0.5; 1)`.
Returns an undefined value if `x` is not finite.
-/
@[extern "lean_float_frexp"] opaque HardwareFloat.frExp : HardwareFloat → HardwareFloat × Int

instance : ToString HardwareFloat where
  toString := HardwareFloat.toString

@[extern "lean_uint64_to_float"]
def UInt64.toHardwareFloat (n : UInt64) : HardwareFloat :=
  HardwareFloat.fromRatParts false n.toNat 1

instance : Repr HardwareFloat where
  reprPrec n prec := if n < ⟨0⟩ then Repr.addAppParen (toString n) prec else toString n

instance : ReprAtom Float  := ⟨⟩

@[extern "sin"] opaque HardwareFloat.sin : HardwareFloat → HardwareFloat
@[extern "cos"] opaque HardwareFloat.cos : HardwareFloat → HardwareFloat
@[extern "tan"] opaque HardwareFloat.tan : HardwareFloat → HardwareFloat
@[extern "asin"] opaque HardwareFloat.asin : HardwareFloat → HardwareFloat
@[extern "acos"] opaque HardwareFloat.acos : HardwareFloat → HardwareFloat
@[extern "atan"] opaque HardwareFloat.atan : HardwareFloat → HardwareFloat
@[extern "atan2"] opaque HardwareFloat.atan2 : HardwareFloat → HardwareFloat → HardwareFloat
@[extern "sinh"] opaque HardwareFloat.sinh : HardwareFloat → HardwareFloat
@[extern "cosh"] opaque HardwareFloat.cosh : HardwareFloat → HardwareFloat
@[extern "tanh"] opaque HardwareFloat.tanh : HardwareFloat → HardwareFloat
@[extern "asinh"] opaque HardwareFloat.asinh : HardwareFloat → HardwareFloat
@[extern "acosh"] opaque HardwareFloat.acosh : HardwareFloat → HardwareFloat
@[extern "atanh"] opaque HardwareFloat.atanh : HardwareFloat → HardwareFloat
@[extern "exp"] opaque HardwareFloat.exp : HardwareFloat → HardwareFloat
@[extern "exp2"] opaque HardwareFloat.exp2 : HardwareFloat → HardwareFloat
@[extern "log"] opaque HardwareFloat.log : HardwareFloat → HardwareFloat
@[extern "log2"] opaque HardwareFloat.log2 : HardwareFloat → HardwareFloat
@[extern "log10"] opaque HardwareFloat.log10 : HardwareFloat → HardwareFloat
@[extern "pow"] opaque HardwareFloat.pow : HardwareFloat → HardwareFloat → HardwareFloat
@[extern "sqrt"] opaque HardwareFloat.sqrt : HardwareFloat → HardwareFloat
@[extern "cbrt"] opaque HardwareFloat.cbrt : HardwareFloat → HardwareFloat
@[extern "ceil"] opaque HardwareFloat.ceil : HardwareFloat → HardwareFloat
@[extern "floor"] opaque HardwareFloat.floor : HardwareFloat → HardwareFloat
@[extern "round"] opaque HardwareFloat.round : HardwareFloat → HardwareFloat

@[extern "fabs"]
def HardwareFloat.abs (x : HardwareFloat) : HardwareFloat :=
  ⟨x.toBits &&& 0x7fff_ffff_ffff_ffff⟩

instance : HomogeneousPow HardwareFloat := ⟨HardwareFloat.pow⟩

instance : Min HardwareFloat := minOfLe

instance : Max HardwareFloat := maxOfLe

/--
Efficiently computes `x * 2^i`.
-/
@[extern "lean_float_scaleb"]
def HardwareFloat.scaleB (x : HardwareFloat) (i : @& Int) : HardwareFloat :=
  if x.isNaN then .makeNan `HardwareFloat.scaleB x x else
  let sign := x.signBit
  let mantissa := x.mantissa
  let newExponent := x.exponentPart.toNat + i
  if newExponent ≥ 2047 then .fromParts sign 2047 0 -- infinity
  else if newExponent < 0 then
    -- just calculate directly
    .fromRatParts sign mantissa.toNat (1 <<< (1022 + 52 - newExponent).natAbs)
  else
    .fromParts sign newExponent.toNat.toUInt64 mantissa
