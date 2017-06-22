theory RedBlackTreeExperiment
imports Main RedBlackTreeExperiment_Impl
begin
subsection {* Type definition *}

typedef (overloaded) ('a, 'b) rbt = "{t :: ('a::linorder, 'b) RedBlackTreeExperiment_Impl.rbt. is_rbt t}"
  morphisms impl_of RedBlackTreeExperiment
proof -
  have "RedBlackTreeExperiment_Impl.Empty \<in> ?rbt" by simp
  then show ?thesis ..
qed
end
