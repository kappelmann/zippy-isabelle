\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Alternating Zippers\<close>
theory ML_Alternating_Zippers
  imports
    ML_Linked_Zippers
begin

ML\<open>
  val pfx_sfx_nargs = ML_Gen.pfx_sfx_nargs
\<close>

ML_gen_file\<open>alternating_zipper_moves.ML\<close>
ML_gen_file\<open>alternating_zipper.ML\<close>
ML_gen_file\<open>pair_alternating_zipper.ML\<close>

ML_gen_file\<open>replace_alternating_zipper_zipper.ML\<close>

ML_gen_file\<open>rotate_alternating_zipper.ML\<close>

ML_gen_file\<open>node.ML\<close>
ML_gen_file\<open>modify_node.ML\<close>

context
  (*FIXME: could be made generic with ML programming*)
  notes [[AllT_args args = ['p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
  and [[imap stop = 6]]
begin
context
  notes [[ZipperT_args args = ['a1, 'a2, 'a3, 'a4, 'a5, 'a6]]]
begin
text \<open>Note: we reload the ML file @{file node.ML} again, just with different parameters.\<close>
ML_gen_file\<open>node.ML\<close>
ML\<open>
  val succ_node_sig = sfx_T_nargs "NODE"
  val succ_node_functor = sfx_T_nargs "Node"
\<close>
end
context
  notes [[AllT_args stop = 5]]
begin
ML_gen_file\<open>modify_node_succ.ML\<close>
end
end

ML_gen_file\<open>alternating_zipper_nodes.ML\<close>
ML_gen_file\<open>alternating_zipper_nodes_zippers.ML\<close>
ML_gen_file\<open>alternating_zipper_nodes_simple_zippers.ML\<close>

end