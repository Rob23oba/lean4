/--
info:
[1, 2, 3, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-/
#guard_msgs in
#eval (ByteArray.mk #[1, 2, 3]).setSize 100

/--
info: [1, 2, 3]
-/
#guard_msgs in
#eval (ByteArray.mk #[1, 2, 3]).setSize 3

/--
info: [1, 2, 3]
-/
#guard_msgs in
#eval (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7]).setSize 3

/--
info: [1, 2, 3, 255, 255, 255, 255]
-/
#guard_msgs in
#eval (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7]).fill 3 4 255

/--
info: [1, 2, 3, 255, 255, 255, 255, 255, 255, 255, 255, 255]
-/
#guard_msgs in
#eval (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7]).fill 3 9 255

#guard ByteArray.sliceEq ⟨#[1, 2, 3, 4, 5, 6]⟩ 3 ⟨#[4, 5, 6, 1, 2, 3]⟩ 0 3
#guard ByteArray.sliceEq ⟨#[2, 2, 2, 2]⟩ 1 ⟨#[2, 2, 2, 2]⟩ 0 3
#guard !ByteArray.sliceEq ⟨#[2, 2, 2, 2]⟩ 2 ⟨#[2, 2, 2, 2]⟩ 0 3
#guard !ByteArray.sliceEq ⟨#[2, 2, 2, 2]⟩ 0 ⟨#[2, 2, 2, 2]⟩ 2 3

#guard ByteArray.mk #[1, 2, 3] == ByteArray.mk #[1, 2, 3]
#guard ByteArray.mk #[1, 2, 3] != ByteArray.mk #[3, 2, 1]
#guard ByteArray.mk #[1, 2, 3] != ByteArray.mk #[1, 2, 3, 4]
#guard ByteArray.mk #[1, 2, 3, 4] != ByteArray.mk #[1, 2, 3]
