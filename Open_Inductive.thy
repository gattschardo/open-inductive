theory Open_Inductive
imports Main
keywords
  "open_inductive"  :: thy_decl and
  "add_intro"       :: thy_decl and
  "open_theorem"    :: thy_decl and
  "show_open"       :: thy_goal and
  "close_inductive" :: thy_decl
begin

text
{*  Title:      Open_Inductive.thy
    Author:     Richard Molitor, IPD Snelting, KIT

Open inductive predicates with flexible sets of introduction rules
and open theorems with inductive proofs on a per-introduction-rule basis.
*}

ML_file "src/result.ML"

ML_file "src/oi_fmt.ML"
ML_file "src/oi_parse.ML"

ML_file "src/open_inductive.ML"

ML {*
val () = Outer_Syntax.local_theory @{command_keyword "open_inductive"}
          "open inductive predicate definition"
          (OI_Parse.open_inductive >> Open_Inductive.open_inductive_cmd)

val () = Outer_Syntax.local_theory @{command_keyword "add_intro"}
          "adds intro rule to open inductive predicate"
          (OI_Parse.add_intro >> Open_Inductive.add_intro_cmd)

val () = Outer_Syntax.local_theory @{command_keyword "open_theorem"}
          "declares open theorem"
          (OI_Parse.open_theorem >> Open_Inductive.open_theorem_cmd)

val () = Outer_Syntax.local_theory_to_proof @{command_keyword "show_open"}
          "shows an open theorem for an intro rule (or directly)"
          (OI_Parse.show >> Open_Inductive.show_open_switch)

val () = Outer_Syntax.local_theory @{command_keyword "close_inductive"}
          "closes an inductive predicate"
          (OI_Parse.close_inductive >> Open_Inductive.close_inductive_cmd)
*}

end
