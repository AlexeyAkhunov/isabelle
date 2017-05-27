theory Exercise_2_6
imports Main
begin
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l a r) = (contents l)@(a#(contents r))"

fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0" |
  "treesum (Node l a r) = (treesum l) + a + (treesum r)"

fun listsum :: "nat list \<Rightarrow> nat" where
  "listsum [] = 0" |
  "listsum (x#xs) = x + (listsum xs)"
  
lemma listsum_app[simp]: "listsum (x@y) = (listsum x) + (listsum y)"
  apply(induction x)
  apply(auto)
  done
  
lemma treelist_sum: "treesum t = listsum(contents t)"
  apply(induction t)
  apply(auto)
  done
