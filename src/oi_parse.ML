(*  Title: oi_parse.ML
    Author: Richard Molitor

Parsers for the Open_Inductive commands.
*)

signature OI_PARSE =
sig
  val open_inductive: (binding * string option * mixfix) list parser
  val add_intro: (bstring * (bstring * string)) parser
  val open_theorem: (bstring * string) parser
  val show: ((bstring * string) * (binding * string option * mixfix) list) parser
  val close_inductive: ((bstring * (binding * string option * mixfix) list) * bstring) parser
end

structure OI_Parse : OI_PARSE =
struct

val open_inductive = Parse.fixes

val add_intro = Parse.name -- (Parse.name -- (@{keyword ":"} |-- Parse.prop))

val open_theorem = Parse.name -- ((Parse.maybe @{keyword "shows"}) |-- Parse.prop)

val show = Parse.name -- Scan.optional (@{keyword "for"} |-- Parse.name) "" --
    Scan.optional (@{keyword "assumes"} |-- Parse.fixes) []

val close_inductive =  Parse.name -- (@{keyword "assumes"} |-- Parse.fixes) --
    (@{keyword "for"} |-- Parse.name)

end
