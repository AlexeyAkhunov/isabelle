theory Exercise_2_9
imports Main
begin
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 0 x = x" |
  "itadd n (Suc m) x = itadd n m (Suc x)" |
  "itadd (Suc m) n x = itadd m n (Suc x)"
  
value "itadd 3 7 0"

lemma itadd_1: "itadd m 0 k = m + k"
  apply(induction m arbitrary: k)
  apply(auto)
  done

lemma "itadd m n k = m + n + k"
  apply(induction m; induction n arbitrary: k)
  apply(auto simp add: itadd_1)
  done
