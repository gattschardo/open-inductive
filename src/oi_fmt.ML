(*  Title: oi_fmt.ML
    Author: Richard Molitor

Formatting utilities for Open_Inductive, mainly to color various syntactic
items for output.
*)

signature OI_FMT =
sig
  val str_typ: Proof.context -> typ -> string

  val color_pred_name: string -> Pretty.T
  val color_intro_name: string -> Pretty.T
  val color_lemma_name: string -> Pretty.T
  val color_typ: Proof.context -> typ -> Pretty.T
end

structure OI_Fmt : OI_FMT =
struct

(*** Pretty-printing ***)

fun str_typ ctxt t = Pretty.string_of (Syntax.pretty_typ ctxt t)

(** Markup **)

val mark_open_pred = Markup.free
val mark_intro = Markup.skolem
val mark_open_lemma = Markup.free
val mark_typ = Markup.bound

val color_pred_name = Pretty.str #> Pretty.mark mark_open_pred
val color_intro_name = Pretty.str #> Pretty.mark mark_intro
val color_lemma_name = Pretty.str #> Pretty.mark mark_open_lemma
fun color_typ ctxt = Syntax.pretty_typ ctxt #> Pretty.mark mark_typ

end
