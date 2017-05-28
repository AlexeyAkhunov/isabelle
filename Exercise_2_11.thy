theory Exercise_2_11
  imports Main
begin
datatype exp = Var | Const int | Add exp exp | Mult exp exp
  
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var v = v" |
  "eval (Const a) _ = a" |
  "eval (Add a b) v = (eval a v) + (eval b v)" |
  "eval (Mult a b) v = (eval a v) * (eval b v)"
  
fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] v = 0" |
  "evalp (x#xs) v = x + v*(evalp xs v)"

fun mulc :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "mulc a [] = []" |
  "mulc a (x#xs) = (a*x)#(mulc a xs)"
  
fun addp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addp [] [] = []" |
  "addp [] ys = ys" |
  "addp xs [] = xs" |
  "addp (x#xs) (y#ys) = (x+y)#(addp xs ys)"
  
fun multp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multp [] [] = []" |
  "multp [] ys = []" |
  "multp xs [] = []" |
  "multp (a#xs) (b#ys) = addp ((a*b)#(addp (mulc b xs) (mulc a ys))) (0#0#(multp xs ys))"
  
fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0,1]" |
  "coeffs (Const a) = [a]" |
  "coeffs (Add a b) = addp (coeffs a) (coeffs b)" |
  "coeffs (Mult a b) = multp (coeffs a) (coeffs b)"

lemma evalp_addp: "evalp (addp p1 p2) v = (evalp p1 v) + (evalp p2 v)"
  apply(induction p1 rule:addp.induct)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_mulc: "evalp (mulc a p) v = a * (evalp p v)"
  apply(induction p)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_multp: "evalp (multp p1 p2) v = (evalp p1 v) * (evalp p2 v)"
  apply(induction p1 rule:multp.induct)
  apply(auto simp add: algebra_simps simp add:evalp_addp simp add: evalp_mulc)
  done

lemma preserve: "evalp(coeffs e) x = eval e x"
  apply(induction e)
  apply(auto simp add: algebra_simps simp add:evalp_addp simp add: evalp_multp)
  done
