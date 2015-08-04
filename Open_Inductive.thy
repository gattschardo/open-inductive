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

ML_file "src/pretty.ML"
ML_file "src/result.ML"
ML_file "src/open_inductive.ML"

end
