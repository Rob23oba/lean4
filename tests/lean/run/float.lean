def nan : Float := Float.ofBits 0x7ff8000000000000

/-- info: NaN -/
#guard_msgs in
#eval nan

#guard nan = nan
#guard nan != nan
#guard (0 : Float) ≠ -0
#guard (0 : Float) == -0
#guard (-0 : Float) ≠ 0
#guard (-0 : Float) == 0

example : nan = nan := rfl
example : nan != nan := rfl

example : (3 : Int64).toFloat * (2 : Int64).toFloat = (6 : Int64).toFloat := rfl
example : (3 : Int64).toFloat * (-2 : Int64).toFloat = (-6 : Int64).toFloat := rfl
example : (0 : Int64).toFloat * -(0 : Int64).toFloat = -(0 : Int64).toFloat := rfl

def tests : Array Float :=
  #[0.0, -0.0, 1.0, -1.0, 1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, 1.3413473814,
    -1.3413473814, 2.5, 5.3, 1.2, 12, 3141, 3141387813478, 1e100, 1e300, -1e300,
    24, 347814738, 341893, -134.431478, 0.3, -0.3491934, 1e-200, 1e-30, -1e-30]

def test : IO Unit :=
  for f in tests do
    let bfloat : Std.BinaryFloat .binary64 := Std.BinaryFloat.decode f.toBits.toBitVec
    for f' in tests do
      let bfloat' : Std.BinaryFloat .binary64 := Std.BinaryFloat.decode f'.toBits.toBitVec
      let res1 := f * f'
      let res2 := bfloat * bfloat'
      if res1.toBits.toBitVec != res2.encode then
        throw (.userError s!"mismatch for {f.toBits.toBitVec} * {f'.toBits.toBitVec}")
      let res1 := f < f'
      let res2 := bfloat < bfloat'
      if res1 != res2 then
        throw (.userError s!"mismatch for {f.toBits.toBitVec} < {f'.toBits.toBitVec}")
      let res1 := f == f'
      let res2 := bfloat == bfloat'
      if res1 != res2 then
        throw (.userError s!"mismatch for {f.toBits.toBitVec} == {f'.toBits.toBitVec}")
      let res1 := f ≤ f'
      let res2 := bfloat ≤ bfloat'
      if res1 != res2 then
        throw (.userError s!"mismatch for {f.toBits.toBitVec} ≤ {f'.toBits.toBitVec}")
    let res1 := -f
    let res2 := -bfloat
    if res1.toBits.toBitVec != res2.encode then
      throw (.userError s!"mismatch for -{f.toBits.toBitVec}")
    let res1 := f.isFinite
    let res2 := bfloat matches .finite ..
    if res1 != res2 then
      throw (.userError s!"mismatch for isFinite {f.toBits.toBitVec}")
    let res1 := f.isNaN
    let res2 := bfloat matches .nan
    if res1 != res2 then
      throw (.userError s!"mismatch for isNaN {f.toBits.toBitVec}")
    let res1 := f.isInf
    let res2 := bfloat matches .inf _
    if res1 != res2 then
      throw (.userError s!"mismatch for isInf {f.toBits.toBitVec}")

#time #eval! test
