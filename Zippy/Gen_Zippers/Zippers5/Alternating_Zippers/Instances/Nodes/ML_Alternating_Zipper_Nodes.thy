\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Alternating Zippers\<close>
theory ML_Alternating_Zipper_Nodes
  imports
    ML_Alternating_Zippers
begin

ML_gen_file\<open>node.ML\<close>
ML_gen_file\<open>modify_node_content.ML\<close>
ML_gen_file\<open>modify_node_next.ML\<close>

context
  (*FIXME: could be made generic with ML programming*)
  notes [[AllT_args args = ['p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
  and [[ZipperT_args args = ['a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
begin
text \<open>Note: we reload the ML file @{file node.ML}, just with different parameters.\<close>
ML_gen_file\<open>node.ML\<close>
ML\<open>
  val succ_node_sig = sfx_T_nargs "NODE"
  val succ_node_functor = sfx_T_nargs "Node"
\<close>
end
context
  notes [[imap stop = 6]]
begin
ML_gen_file\<open>instantiate_node_succ.ML\<close>
end

ML_gen_file\<open>alternating_zipper_nodes.ML\<close>
ML_gen_file\<open>alternating_zipper_nodes_zippers.ML\<close>
ML_gen_file\<open>alternating_zipper_nodes_simple_zippers.ML\<close>

end