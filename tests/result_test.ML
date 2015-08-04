
val fr0 = first_res (I: bool option -> bool option) false []
val () = assert_eq fr0 (Err false)

val fr1 = first_res I false
val fr1_r = fr1 [NONE, NONE, SOME 1, NONE]
val () = assert_eq fr1_r (Res 1)
val fr1_f = fr1 [NONE, NONE]
val () = assert_eq fr1_f (Err false)

val fr2 = first_res (fn x => if x = 2 then SOME 4 else NONE) false
val fr2_r = fr2 [4, 3, 2, 1, 0]
val () = assert_eq fr2_r (Res 4)
val fr2_f = fr2 [4, 4, 4, 4, 4]
val () = assert_eq fr2_f (Err false)

val zip0 = []: (bool, bool) result list
val ze0 = zip_errors zip0
val () = assert_eq ze0 []
val zr0 = zip_results zip0
val () = assert_eq zr0 []

val zip1 = [Res 1, Err 1, Res 1, Err 2, Res 1, Err 3, Res 1, Err 4]
val ze1 = zip_errors zip1
val () = assert_eq ze1 [1, 2, 3, 4]
val zr1 = zip_results zip1
val () = assert_eq zr1 [1, 1, 1, 1]

val zip2 = [Err 1, Res 1, Err 1, Res 2, Err 1, Res 3, Err 1, Res 4]
val ze2 = zip_errors zip2
val () = assert_eq ze2 [1, 1, 1, 1]
val zr2 = zip_results zip2
val () = assert_eq zr2 [1, 2, 3, 4]