(*** Pretty-printing ***)

fun pretty_thms ctxt ts =
  map (Display.pretty_thm_item ctxt) ts |> Pretty.fbreaks |> Pretty.block

fun pretty_typs ctxt ts =
  Pretty.block (map (Syntax.pretty_typ ctxt) ts)

fun pretty_terms ctxt ts =
  Pretty.block (map (Syntax.pretty_term ctxt) ts)

fun str_typ ctxt t = Pretty.string_of (pretty_typs ctxt [t])

(** Markup **)

val mark_open_pred = Markup.free
val mark_intro = Markup.skolem
val mark_open_lemma = Markup.free
val mark_typ = Markup.bound

val pretty_pred = Pretty.str #> Pretty.mark mark_open_pred
val pretty_intro = Pretty.str #> Pretty.mark mark_intro
val pretty_lemma = Pretty.str #> Pretty.mark mark_open_lemma
fun pretty_typ ctxt = Syntax.pretty_typ ctxt #> Pretty.mark mark_typ
