
val fr0 = Result.first (I: bool option -> bool option) false []
val () = assert_eq fr0 (Result.Error false)

val fr1 = Result.first I false
val fr1_r = fr1 [NONE, NONE, SOME 1, NONE]
val () = assert_eq fr1_r (Result.Ok 1)
val fr1_f = fr1 [NONE, NONE]
val () = assert_eq fr1_f (Result.Error false)

val fr2 = Result.first (fn x => if x = 2 then SOME 4 else NONE) false
val fr2_r = fr2 [4, 3, 2, 1, 0]
val () = assert_eq fr2_r (Result.Ok 4)
val fr2_f = fr2 [4, 4, 4, 4, 4]
val () = assert_eq fr2_f (Result.Error false)

val zip0 = []: (bool, bool) Result.t list
val ze0 = Result.zip_errors zip0
val () = assert_eq ze0 []
val zr0 = Result.zip_results zip0
val () = assert_eq zr0 []

val zip1 =
  [Result.Ok 1, Result.Error 1, Result.Ok 1, Result.Error 2,
   Result.Ok 1, Result.Error 3, Result.Ok 1, Result.Error 4]
val ze1 = Result.zip_errors zip1
val () = assert_eq ze1 [1, 2, 3, 4]
val zr1 = Result.zip_results zip1
val () = assert_eq zr1 [1, 1, 1, 1]

val zip2 =
  [Result.Error 1, Result.Ok 1, Result.Error 1, Result.Ok 2,
   Result.Error 1, Result.Ok 3, Result.Error 1, Result.Ok 4]
val ze2 = Result.zip_errors zip2
val () = assert_eq ze2 [1, 1, 1, 1]
val zr2 = Result.zip_results zip2
val () = assert_eq zr2 [1, 2, 3, 4]
