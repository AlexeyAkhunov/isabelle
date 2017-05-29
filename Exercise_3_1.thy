theory Exercise_3_1
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}" |
  "set (Node l a r) = (set l) \<union> (set r) \<union> {a}"

fun min_opt :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
  "min_opt None None = None" |
  "min_opt (Some a) None = Some a" |
  "min_opt None (Some a) = Some a" |
  "min_opt (Some a) (Some b) = Some (min a b)"

fun max_opt :: "int option \<Rightarrow> int option \<Rightarrow> int option" where
  "max_opt None None = None" |
  "max_opt (Some a) None = Some a" |
  "max_opt None (Some a) = Some a" |
  "max_opt (Some a) (Some b) = Some (max a b)"
  
fun le_opt :: "int option \<Rightarrow> int \<Rightarrow> bool" where
  "le_opt None _ = True" |
  "le_opt (Some a) b = (a\<le>b)"

fun ge_opt :: "int option \<Rightarrow> int \<Rightarrow> bool" where
  "ge_opt None _ = True" |
  "ge_opt (Some a) b = (a\<ge>b)"  
 
fun min_tree :: "int tree \<Rightarrow> int option" where
  "min_tree Tip = None" |
  "min_tree (Node l a r) = min_opt (min_opt (min_tree l) (Some a)) (min_tree r)"

fun max_tree :: "int tree \<Rightarrow> int option" where
  "max_tree Tip = None" |
  "max_tree (Node l a r) = max_opt (max_opt (max_tree l) (Some a)) (max_tree r)"
  
fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node l a r) = ((le_opt (max_tree l) a) \<and> (ge_opt (min_tree r) a) \<and> (ord l) \<and> (ord r))"
  
fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins a Tip = Node Tip a Tip" |
  "ins a (Node l b r) = (if (a=b) then (Node l b r) else (if (a<b) then (Node (ins a l) b r) else (Node l b (ins a r))))"

lemma "set(ins x t) = {x} \<union> (set t)"
  apply(induction t)
  apply(auto)
  done

lemma max_opt_none: "max_opt None x = max_opt x None"
  apply(induction x)
  apply(auto)
  done
    
lemma max_opt_some: "max_opt (Some a) x = max_opt x (Some a)"
  apply(induction x)
  apply(auto)
  done

lemma max_opt_none_2: "max_opt(max_opt x y) None = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done
    
lemma max_opt_none_3: "max_opt(max_opt x None) y = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma max_opt_none_4: "max_opt x (max_opt y None) = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done
    
lemma max_opt_none_5: "max_opt (max_opt None x) y = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma max_opt_none_6: "max_opt (max_opt x None) y = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma max_opt_none_7: "max_opt x (max_opt None y) = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done
    
lemma max_opt_none_8: "max_opt None (max_opt x y) = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma max_opt_commutative: "max_opt x y = max_opt y x"
  apply(induction x)
  apply(auto simp add: max_opt_none, simp add: max_opt_some)
  done

lemma max_opt_swap: "max_opt(max_opt x y) z = max_opt(max_opt x z) y"
  apply(induction x)
  apply(auto simp add: max_opt_none_5, simp add:max_opt_commutative)
  apply(induction y)
  apply(auto simp add: max_opt_none_5, simp add: max_opt_none_2)
  apply(induction z)
  apply(auto)
  done
    
lemma max_opt_associative: "max_opt x (max_opt y z) = max_opt (max_opt x y) z"
  apply(induction x)
  apply(auto simp add:max_opt_none, simp add:max_opt_none_2, simp add:max_opt_none_3)
  apply(induction y)
  apply(auto simp add:max_opt_none, simp add:max_opt_none_4)
  apply(induction z)
  apply(auto)
  done

lemma max_opt_some_2: "max_opt(max_opt x (Some y)) z = max_opt x (max_opt z (Some y))"
  apply(induction x)
  apply(auto simp add:max_opt_none_7, simp add:max_opt_none_8, simp add:max_opt_some)
  apply(induction z)
  apply(auto)
  done
    
lemma max_opt_dense: "max_opt x (max_opt y z) = max_opt(max_opt x y) z"
  apply(induction x)
  apply(simp_all add:max_opt_none_8)
  apply(induction y)
  apply(auto simp add:max_opt_some)
  apply(auto simp add:max_opt_some_2)
  apply(auto simp add:max_opt_associative)
  done
    
lemma max_opt_double_some: "max_opt (max_opt x (Some y)) (Some z) = max_opt x (Some (max y z))"
  apply(induction x)
  apply(simp_all add:max_opt_none_8)
  done

lemma max_tree_ins: "max_tree(ins i t) = max_opt (Some i) (max_tree t)"
  apply(induction t)
  apply(auto simp add: max_opt_some)
  apply(auto simp add: max_opt_some_2)
  apply(auto simp add: max_opt_dense)
  apply(auto simp add: max_opt_double_some)
  done
    
lemma le_opt_max_opt: "le_opt x z \<Longrightarrow> le_opt y z \<Longrightarrow> le_opt(max_opt x y) z"
  apply(induction x; induction y)
  apply(auto)
  done

lemma min_opt_none: "min_opt None x = min_opt x None"
  apply(induction x)
  apply(auto)
  done
    
lemma min_opt_some: "min_opt (Some a) x = min_opt x (Some a)"
  apply(induction x)
  apply(auto)
  done

lemma min_opt_none_2: "min_opt(min_opt x y) None = min_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done
    
lemma min_opt_none_3: "min_opt(min_opt x None) y = min_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma min_opt_none_4: "min_opt x (min_opt y None) = min_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done
    
lemma min_opt_none_5: "min_opt (min_opt None x) y = min_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma max_opt_none_6: "max_opt (max_opt x None) y = max_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma min_opt_none_7: "min_opt x (min_opt None y) = min_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done
    
lemma min_opt_none_8: "min_opt None (min_opt x y) = min_opt x y"
  apply(induction x; induction y)
  apply(auto)
  done

lemma min_opt_commutative: "min_opt x y = min_opt y x"
  apply(induction x)
  apply(auto simp add: min_opt_none, simp add: min_opt_some)
  done

lemma min_opt_swap: "min_opt(min_opt x y) z = min_opt(min_opt x z) y"
  apply(induction x)
  apply(auto simp add: min_opt_none_5, simp add:min_opt_commutative)
  apply(induction y)
  apply(auto simp add: min_opt_none_5, simp add: min_opt_none_2)
  apply(induction z)
  apply(auto)
  done

lemma min_opt_associative: "min_opt x (min_opt y z) = min_opt (min_opt x y) z"
  apply(induction x)
  apply(auto simp add:min_opt_none, simp add:min_opt_none_2, simp add:min_opt_none_3)
  apply(induction y)
  apply(auto simp add:min_opt_none, simp add:min_opt_none_4)
  apply(induction z)
  apply(auto)
  done

lemma min_opt_some_2: "min_opt(min_opt x (Some y)) z = min_opt x (min_opt z (Some y))"
  apply(induction x)
  apply(auto simp add:min_opt_none_7, simp add:min_opt_none_8, simp add:min_opt_some)
  apply(induction z)
  apply(auto)
  done
    
lemma min_opt_dense: "min_opt x (min_opt y z) = min_opt(min_opt x y) z"
  apply(induction x)
  apply(simp_all add:min_opt_none_8)
  apply(induction y)
  apply(auto simp add:min_opt_some)
  apply(auto simp add:min_opt_some_2)
  apply(auto simp add:min_opt_associative)
  done
    
lemma min_opt_double_some: "min_opt (min_opt x (Some y)) (Some z) = min_opt x (Some (min y z))"
  apply(induction x)
  apply(simp_all add:min_opt_none_8)
  done

lemma min_tree_ins: "min_tree(ins i t) = min_opt (Some i) (min_tree t)"
  apply(induction t)
  apply(auto simp add: min_opt_some)
  apply(auto simp add: min_opt_some_2)
  apply(auto simp add: min_opt_dense)
  apply(auto simp add: min_opt_double_some)
  done
    
lemma ge_opt_min_opt: "ge_opt x z \<Longrightarrow> ge_opt y z \<Longrightarrow> ge_opt(min_opt x y) z"
  apply(induction x; induction y)
  apply(auto)
  done
    

lemma "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t)
  apply(auto simp add:max_tree_ins)
  apply(auto simp add:le_opt_max_opt)
  apply(auto simp add:min_tree_ins)
  apply(auto simp add:ge_opt_min_opt)
  done
