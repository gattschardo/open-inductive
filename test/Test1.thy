theory Test1
imports Main "../Open_Inductive"
begin

consts a :: nat
consts R :: "nat rel"

lemma a_in_Field_R: "a \<in> Field R" sorry

lemma FieldI1: "(i, j) \<in> R \<Longrightarrow> i \<in> Field R"
unfolding Field_def by auto

(* open_inductive P :: "nat \<Rightarrow> bool" *)
open_inductive P

add_intro P base: "P a"
add_intro P forward: "P x \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> P y"
add_intro P backward: "P x \<Longrightarrow> (y,x) \<in> R \<Longrightarrow> P y"


open_theorem P_Field shows "P x \<Longrightarrow> x \<in> Field R"

show_open P_Field for base by (rule a_in_Field_R)
show_open P_Field for forward
proof-
  fix x y
  assume "P x" and "x \<in> Field R" and "(x, y) \<in> R"
  thus "y \<in> Field R" by (intro FieldI2)
qed
show_open P_Field for backward
proof-
  fix x y
  assume "P x" and "x \<in> Field R" and "(y, x) \<in> R"
  thus "y \<in> Field R" by (intro FieldI1)
qed

close_inductive P assumes base forward for P\<^sub>1\<^sub>2'
close_inductive P assumes base forward backward for P\<^sub>1\<^sub>2\<^sub>3'


end
