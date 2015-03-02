theory Test
imports Main "../../Open_Inductive"
begin

consts a :: nat
consts R :: "nat rel"

lemma a_in_Field_R: "a \<in> Field R" sorry

lemma FieldI1: "(i, j) \<in> R \<Longrightarrow> i \<in> Field R"
unfolding Field_def by auto

text_raw {*\DefineSnippet{inductive1}{*}
inductive P\<^sub>1\<^sub>2 where
  "P\<^sub>1\<^sub>2 a" | "P\<^sub>1\<^sub>2 x \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> P\<^sub>1\<^sub>2 y"
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{inductive2}{*}
inductive P\<^sub>1\<^sub>2\<^sub>3 where
  "P\<^sub>1\<^sub>2\<^sub>3 a" | "P\<^sub>1\<^sub>2\<^sub>3 x \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> P\<^sub>1\<^sub>2\<^sub>3 y"
          | "P\<^sub>1\<^sub>2\<^sub>3 x \<Longrightarrow> (y,x) \<in> R \<Longrightarrow> P\<^sub>1\<^sub>2\<^sub>3 y"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{proof1}{*}
theorem P\<^sub>1\<^sub>2_Field: "P\<^sub>1\<^sub>2 x \<Longrightarrow> x \<in> Field R"
proof(induction rule: P\<^sub>1\<^sub>2.induct)
  show "a \<in> Field R" by (rule a_in_Field_R)
next
  fix x y
  assume "P\<^sub>1\<^sub>2 x" and  "x \<in> Field R" and "(x, y) \<in> R"
  thus "y \<in> Field R" by (intro FieldI2)
qed
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{proof2}{*}
theorem P\<^sub>1\<^sub>2\<^sub>3_Field: "P\<^sub>1\<^sub>2\<^sub>3 x \<Longrightarrow> x \<in> Field R"
proof(induction rule: P\<^sub>1\<^sub>2\<^sub>3.induct)
  show "a \<in> Field R" by (rule a_in_Field_R)
next
  fix x y
  assume "P\<^sub>1\<^sub>2\<^sub>3 x" and "x \<in> Field R" and "(x, y) \<in> R"
  thus "y \<in> Field R" by (intro FieldI2)
next
  fix x y
  assume "P\<^sub>1\<^sub>2\<^sub>3 x" and "x \<in> Field R" and "(y, x) \<in> R"
  thus "y \<in> Field R"  by (intro FieldI1)
qed
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{open_inductive}{*}
open_inductive P :: "nat \<Rightarrow> bool"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{add_intros}{*}
add_intro P base: "P a"
add_intro P forward: "P x \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> P y"
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{add_intros2}{*}
add_intro P backward: "P x \<Longrightarrow> (y,x) \<in> R \<Longrightarrow> P y"
text_raw {*}%EndSnippet*}


text_raw {*\DefineSnippet{open_theorem}{*}
open_theorem P_Field shows "P x \<Longrightarrow> x \<in> Field R"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{show_open}{*}
show_open P_Field for base by (rule a_in_Field_R)
show_open P_Field for forward
proof-
  fix x y
  assume "P x" and "x \<in> Field R" and "(x, y) \<in> R"
  thus "y \<in> Field R" by (intro FieldI2)
qed
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{show_open2}{*}
show_open P_Field for backward
proof-
  fix x y
  assume "P x" and "x \<in> Field R" and "(y, x) \<in> R"
  thus "y \<in> Field R" by (intro FieldI1)
qed
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{close_inductive}{*}
close_inductive P assumes base forward for P\<^sub>1\<^sub>2'
text_raw {*}%EndSnippet*}
text_raw {*\DefineSnippet{close_inductive2}{*}
close_inductive P assumes base forward backward for P\<^sub>1\<^sub>2\<^sub>3'
text_raw {*}%EndSnippet*}

lemma "P\<^sub>1\<^sub>2 = P\<^sub>1\<^sub>2'" unfolding P\<^sub>1\<^sub>2_def P\<^sub>1\<^sub>2'_def.. 


end
