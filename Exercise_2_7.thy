theory Exercise_2_7
imports Main
begin   
datatype 'a tree2 = Tip 'a | Node "'a tree2" "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror (Tip x) = Tip x" |
  "mirror (Node l r) = Node (mirror r) (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip x) = [x]" |
  "pre_order (Node l r) = (pre_order l) @ (pre_order r)"
  
fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip x) = [x]" |
  "post_order (Node l r) = (post_order r) @ (post_order l)"
  
value "pre_order (Node (Tip (Suc 0)) (Tip 0))"
  
value "post_order (Node (Tip (Suc 0)) (Tip 0))"
    
lemma "pre_order(mirror t) = post_order t"
  apply(induction t)
  apply(auto)
  done

lemma "pre_order(mirror t) = rev(pre_order t)"
  apply(induction t)
  apply(auto)
  done
    
lemma "post_order(mirror t) = pre_order t"
  apply(induction t)
  apply(auto)
  done
    
lemma "post_order(mirror t) = rev(post_order t)"
  apply(induction t)
  apply(auto)
  done
