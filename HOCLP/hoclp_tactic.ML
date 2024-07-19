(*  Title:      HOCLP/hoclp_tactic.ML
    Author:     Kevin Kappelmann
*)
structure HOCLP_Tactic =
struct

val mk_tac_app_res_from_tactical = Make_Tac_App_Result(fn path_zipper => fn res_children =>
  let
    val (ET.Tree children) = get_path_zipper_zipper path_zipper |> get_zipper_content |> get_node_children
    val _ = @{print} children
  in res_children end)

fun tac_from_tactical prio_tac_ret tac {prio, content = path_zipper} =
  let
    val state = get_path_zipper_state path_zipper
    val statesq = tac state
    val tac_app = tac_app mk_tac_app_res_from_tactical
    val state_statesq = Seq.pull statesq
    val path_zipper =
      state_statesq
      |> Option.map (fst
      #> goal_cluster_state
      #> General_Util.flip goal_cluster prio_tac_ret
      #> leaf_tree_node
      #> single
      #> tree_nodes
      #> tree
      #> tac_tree_node tac_app
      #> General_Util.flip path_zipper_insert_tac_tree_node path_zipper)
    val prio = prio - 1
    val prio_tac = Option.map (fn (_,statesq) =>
      tac_from_tactical prio_tac_ret (K statesq)
      |> prio_content prio)
      state_statesq
    val prio_tac_ret = HOCLPDT.prio_tac_ret (K prio_tac)
    val path_zipper = Option.map ((
      map_goal_cluster_prio_tac_ret
      #> map_node_content
      #> map_zipper_content
      #> map_path_zipper_zipper) (K prio_tac_ret)) path_zipper
  in path_zipper end

fun leaf_tac_from_tactical tac = tac_from_tactical (prio_tac_ret (K NONE)) tac

end
