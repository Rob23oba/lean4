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
