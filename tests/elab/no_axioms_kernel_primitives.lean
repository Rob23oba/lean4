/-!
All of the kernel primitives don't depend on any axioms.

List taken from `primitiveTargets` in `Lake.CLI.Check`
-/

/-- info: 'Nat.zero' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.zero
/-- info: 'Nat.succ' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.succ
/-- info: 'Nat.add' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.add
/-- info: 'Nat.sub' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.sub
/-- info: 'Nat.mul' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.mul
/-- info: 'Nat.pow' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.pow
/-- info: 'Nat.gcd' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.gcd
/-- info: 'Nat.mod' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.mod
/-- info: 'Nat.div' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.div
/-- info: 'Nat.beq' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.beq
/-- info: 'Nat.ble' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.ble
/-- info: 'Nat.land' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.land
/-- info: 'Nat.lor' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.lor
/-- info: 'Nat.xor' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.xor
/-- info: 'Nat.shiftLeft' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.shiftLeft
/-- info: 'Nat.shiftRight' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.shiftRight
/-- info: 'Char.ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms Char.ofNat
/-- info: 'String.ofList' does not depend on any axioms -/
#guard_msgs in #print axioms String.ofList
/-- info: 'eagerReduce' does not depend on any axioms -/
#guard_msgs in #print axioms eagerReduce
/-- info: 'optParam' does not depend on any axioms -/
#guard_msgs in #print axioms optParam
/-- info: 'autoParam' does not depend on any axioms -/
#guard_msgs in #print axioms autoParam
/-- info: 'semiOutParam' does not depend on any axioms -/
#guard_msgs in #print axioms semiOutParam
/-- info: 'outParam' does not depend on any axioms -/
#guard_msgs in #print axioms outParam
