\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Alternating Zippers\<close>
theory ML_Alternating_Zippers
  imports
    ML_Zippers
begin

ML_file'\<open>alternating_zippers_moves.ML\<close>

ML_file'\<open>alternating_zippers.ML\<close>
ML_file'\<open>pair_alternating_zippers.ML\<close>

ML_file'\<open>replace_alternating_zippers_zipper.ML\<close>

ML_file'\<open>rotate_alternating_zippers.ML\<close>

ML_file'\<open>node.ML\<close>
ML_file'\<open>modify_node.ML\<close>

context
  notes [[PolyT_args args = ['a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
  and [[T_args args = ['p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
  and [[imap stop = 6]]
begin
ML_file'\<open>node.ML\<close>
context
  notes [[T_args stop = 5]]
begin
ML_file'\<open>modify_node_succ.ML\<close>
end
end

ML_file'\<open>alternating_zippers_nodes.ML\<close>
ML_file'\<open>alternating_zippers_nodes_zippers.ML\<close>
ML_file'\<open>alternating_zippers_nodes_simple_zippers.ML\<close>

end