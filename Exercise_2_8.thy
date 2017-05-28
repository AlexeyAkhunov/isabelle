theory Exercise_2_8
imports Main
begin
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ [] = []" |
  "intersperse _ [x] = [x]" |
  "intersperse a (x#(y#xs)) = x#(a#(intersperse a (y#xs)))"
  
value "intersperse 0 [(Suc 0), (Suc 0), (Suc 0)]"
  
lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done

