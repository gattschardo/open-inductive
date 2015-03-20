theory Open_Arith_Eval
imports Open_Inductive
begin

datatype expr =
  Const int
| Add expr expr
| Sub expr expr

open_inductive eval::"expr \<Rightarrow> int \<Rightarrow> bool"
add_intro eval const: "eval (Const n) n"
add_intro eval add: "eval a ra \<Longrightarrow> eval b rb \<Longrightarrow> ra + rb = n \<Longrightarrow> eval (Add a b) n"
add_intro eval sub: "eval a ra \<Longrightarrow> eval b rb \<Longrightarrow> ra - rb = n \<Longrightarrow> eval (Sub a b) n"

open_theorem double_add shows "eval e n \<Longrightarrow> eval (Add e e) (2 * n)"

show_open double_add assumes add
by (rule eval.add, simp_all, presburger)

fun cdouble where
  "cdouble (Const n) = Const (2 * n)"
| "cdouble (Add a b) = Add (cdouble a) (cdouble b)"
| "cdouble (Sub a b) = Sub (cdouble a) (cdouble b)"

open_theorem double shows "eval e n \<Longrightarrow> eval (cdouble e) (2 * n)"

show_open double for const
proof-
  fix n
  have "cdouble (Const n) = Const (2 * n)" by (rule cdouble.simps(1))
  with eval.const show "eval (cdouble (Const n)) (2 * n)" by simp
qed

show_open double for add
proof-
  fix a ra b rb n
  assume a: "eval (cdouble a) (2 * ra)"
    and b: "eval (cdouble b) (2 * rb)"
    and ab: "ra + rb = n"
  have "cdouble (Add a b) = Add (cdouble a) (cdouble b)" by (rule cdouble.simps(2))
  with eval.add a b ab show "eval (cdouble (Add a b)) (2 * n)" by simp
qed

show_open double for sub
proof-
  fix a ra b rb n
  assume a: "eval (cdouble a) (2 * ra)"
    and b: "eval (cdouble b) (2 * rb)"
    and ab: "ra - rb = n"
  have "cdouble (Sub a b) = Sub (cdouble a) (cdouble b)" by (rule cdouble.simps(3))
  with eval.sub a b ab show "eval (cdouble (Sub a b)) (2 * n)" by simp
qed

fun swap where
  "swap (Const n) = Const n"
| "swap (Add a b) = Add (swap b) (swap a)"
| "swap (Sub a b) = Sub (swap b) (swap a)"

open_theorem commutes shows "eval e n \<Longrightarrow> eval (swap e) n"

show_open commutes for const
proof-
  fix n
  have "swap (Const n) = Const n" by (rule swap.simps(1))
  with eval.const show "eval (swap (Const n)) n" by simp
qed

show_open commutes for add
proof-
  fix a ra b rb n
  assume a: "eval (swap a) ra"
    and b: "eval (swap b) rb"
    and ab: "ra + rb = n"
  have "swap (Add a b) = Add (swap b) (swap a)" by (rule swap.simps(2))
  with eval.add a b ab show "eval (swap (Add a b)) n" by simp
qed

fun andf where
  "andf True True = True"
| "andf _ _ = False"

fun no_add where
  "no_add (Const _) = True"
| "no_add (Add _ _) = False"
| "no_add (Sub a b) = andf (no_add a) (no_add b)"

fun rem_add where
  "rem_add (Const n) = Const n"
| "rem_add (Add a b) = Sub (rem_add a) (Sub (Const 0) (rem_add b))"
| "rem_add (Sub a b) = Sub (rem_add a) (rem_add b)"

lemma rem_add_removes: "no_add (rem_add e)"
  by (induction e) auto

open_theorem rem_add_correct shows "eval e n \<Longrightarrow> eval (rem_add e) n"

show_open rem_add_correct for const
  using eval.const by simp

show_open rem_add_correct for add
  assumes sub const
  apply simp
  apply (erule eval.sub)
  apply (rule eval.sub)
  apply (rule eval.const)
  apply simp_all
  apply presburger
  done

show_open rem_add_correct for sub
  using eval.sub by simp

close_inductive eval assumes const and add for eval
close_inductive eval assumes const add and sub for eval'

thm eval.induct
thm eval.commutes
thm commutes
thm eval'.double_add

end
