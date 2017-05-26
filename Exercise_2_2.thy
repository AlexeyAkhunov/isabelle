theory Exercise_2_2
  imports Main
begin
fun add :: "nat\<Rightarrow>nat\<Rightarrow>nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"

lemma add_associative: "add x (add y z) = add (add x y) z"
  apply(induction x)
  apply(auto)
  done

lemma add_right_zero[simp]: "add y 0 = y"
  apply(induction y)
  apply(auto)
  done
    
lemma add_right[simp]: "add m (Suc n) = Suc(add m n)"
  apply(induction m)
  apply(auto)
  done
    
lemma add_commutative: "add x y = add y x"
  apply(induction x)
  apply(auto)
  done

fun double :: "nat\<Rightarrow>nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc(Suc(double n))"
  
lemma double_add: "double m = add m m"
  apply(induction m)
  apply(auto)
  done

    