(** Result Datatype (Result in Rust, Either in Haskell) **)

datatype ('a, 'b) result =
  Err of 'a
| Res of 'b

fun first_res _ err [] = Err err
  | first_res f err (x::xs) =
      case f x of
        SOME r => Res r
      | NONE => first_res f err xs

fun zip_errors [] = []
  | zip_errors (Err x::xs) = x::zip_errors xs
  | zip_errors (Res _::xs) = zip_errors xs

fun zip_results [] = []
  | zip_results (Err _::xs) = zip_results xs
  | zip_results (Res x::xs) = x::zip_results xs
