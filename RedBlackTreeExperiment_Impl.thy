theory RedBlackTreeExperiment_Impl
imports Main
begin
subsection {* Datatype of RB trees *}

datatype color = R | B
datatype ('a, 'b) rbt = Empty | Branch color "('a, 'b) rbt" 'a 'b "('a, 'b) rbt"

subsection {* Tree properties *}

subsubsection {* Content of a tree *}

primrec entries :: "('a, 'b) rbt => ('a \<times> 'b) list"
where 
  "entries Empty = []"
| "entries (Branch _ l k v r) = entries l @ (k,v) # entries r"
  
definition keys :: "('a, 'b) rbt => 'a list" where
  "keys t = map fst (entries t)"  

subsubsection {* Search tree properties *}
  
context ord begin

definition rbt_less :: "'a => ('a, 'b) rbt => bool"
where
  rbt_less_prop: "rbt_less k t \<longleftrightarrow> (\<forall>x\<in>set (keys t). x < k)"
  
abbreviation rbt_less_symbol (infix "|\<guillemotleft>" 50)
where "t |\<guillemotleft> x \<equiv> rbt_less x t"

definition rbt_greater :: "'a => ('a, 'b) rbt => bool" (infix "\<guillemotleft>|" 50) 
where
  rbt_greater_prop: "rbt_greater k t = (\<forall>x\<in>set (keys t). k < x)"  
 
primrec rbt_sorted :: "('a, 'b) rbt => bool"
where
  "rbt_sorted Empty = True"
| "rbt_sorted (Branch c l k v r) = (l |\<guillemotleft> k \<and> k \<guillemotleft>| r \<and> rbt_sorted l \<and> rbt_sorted r)"

end

subsubsection {* Red-black properties *}
primrec color_of :: "('a, 'b) rbt => color"
where
  "color_of Empty = B"
| "color_of (Branch c _ _ _ _) = c"

primrec bheight :: "('a,'b) rbt => nat"
where
  "bheight Empty = 0"
| "bheight (Branch c lt k v rt) = (if c = B then Suc (bheight lt) else bheight lt)" 
 
primrec inv1 :: "('a, 'b) rbt => bool"
where
  "inv1 Empty = True"
| "inv1 (Branch c lt k v rt) \<longleftrightarrow> inv1 lt \<and> inv1 rt \<and> (c = B \<or> color_of lt = B \<and> color_of rt = B)"  

primrec inv2 :: "('a, 'b) rbt => bool"
where
  "inv2 Empty = True"
| "inv2 (Branch c lt k v rt) = (inv2 lt \<and> inv2 rt \<and> bheight lt = bheight rt)"

context ord begin

definition is_rbt :: "('a, 'b) rbt => bool" where
  "is_rbt t \<longleftrightarrow> inv1 t \<and> inv2 t \<and> color_of t = B \<and> rbt_sorted t"

end

end
