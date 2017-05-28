theory Exercise_2_10
  imports Main
begin
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = Suc 0" |
  "nodes (Node l r) = Suc ((nodes l) + (nodes r))"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

lemma explode_size: "nodes (explode n t) = (2^n)*(nodes t) + (2^n) - 1"
  apply(induction n arbitrary:t)
  apply(auto simp add: algebra_simps)
  done
