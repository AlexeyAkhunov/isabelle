theory Exercise_2_4
imports Main
begin
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]" |
  "snoc (x#xs) y = (x#(snoc xs y))"

value "snoc [1::int,2,3,4] 5"
  
fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x#xs) = snoc (reverse xs) x"

lemma reverse_snoc[simp] : "reverse (snoc xs a) = a#(reverse xs)"
  apply(induction xs)
  apply(auto)
  done
    
lemma double_reverse: "reverse(reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done
