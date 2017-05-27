theory Exercise_2_3
  imports Main
begin
fun count ::"'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0" |
  "count y (x#xs) = (if (x=y) then (Suc (count y xs)) else (count y xs))"
  
value "count (2::int) [1,2,3,4,2,2]"

lemma count_less_length: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done
