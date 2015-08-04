val ctxt = @{context}

val p0 = pretty_thms ctxt []
val () = Pretty.writeln p0

val p1 = pretty_thms ctxt [@{thm TrueI}, @{thm TrueE}, @{thm TrueE}]
val () = Pretty.writeln p1

val ty0 = pretty_typs ctxt []
val () = Pretty.writeln ty0

val ty1 = pretty_typs ctxt [@{typ bool}, @{typ int}, @{typ nat}]
val () = Pretty.writeln ty1

val t0 = pretty_terms ctxt []
val () = Pretty.writeln t0

val t1 = pretty_terms ctxt [@{term "True ==> False"}, @{term "A \<and> B ==> C"}, @{term "D == D"}]
val () = Pretty.writeln t1

val tys0 = str_typ ctxt @{typ bool}
val () = writeln tys0

val tys1 = str_typ ctxt @{typ "int => nat => bool"}
val () = writeln tys1