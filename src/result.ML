(*  Title: result.ML
    Author: Richard Molitor

A Result datatype that can contain two different types depending on success or
failure of an operation. This is known as Result in Rust, Either in Haskell.

This is useful when a errors are the norm for certain inputs and a string as
failure type such as Isabelle provides with the ERROR exception (raised by fun
error) is not sufficient.
*)

signature RESULT =
sig
  datatype ('a, 'b) t =
    Ok of 'a
  | Error of 'b

  val first: ('c -> 'a option) -> 'b -> 'c list -> ('a, 'b) t

  val zip_results: ('a, 'b) t list -> 'a list
  val zip_errors: ('a, 'b) t list -> 'b list
end

structure Result : RESULT =
struct
datatype ('a, 'b) t =
  Ok of 'a
| Error of 'b

fun first _ err [] = Error err
  | first f err (x::xs) =
      case f x of
        SOME r => Ok r
      | NONE => first f err xs

fun zip_results [] = []
  | zip_results (Error _::xs) = zip_results xs
  | zip_results (Ok x::xs) = x::zip_results xs

fun zip_errors [] = []
  | zip_errors (Error x::xs) = x::zip_errors xs
  | zip_errors (Ok _::xs) = zip_errors xs
end
