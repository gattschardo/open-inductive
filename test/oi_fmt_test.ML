val ctxt = @{context}
val pw = Pretty.writeln


val tys0 = OI_Fmt.str_typ ctxt @{typ bool}
val () = writeln tys0

val tys1 = OI_Fmt.str_typ ctxt @{typ "int => nat => bool"}
val () = writeln tys1

val cp0 = OI_Fmt.color_pred_name "pred"
val () = pw cp0

val ci0 = OI_Fmt.color_intro_name "intro"
val () = pw ci0

val cl0 = OI_Fmt.color_lemma_name "lemma"
val () = pw cl0

val ct0 = OI_Fmt.color_typ ctxt @{typ "nat => bool"}
val () = pw ct0