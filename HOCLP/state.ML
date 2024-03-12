(*  Title:      HOCLP/state.ML
    Author:     Kevin Kappelmann
*)
structure State =
struct

(* structure Goal_Cluster_State =
struct
  type t = thm
  val subgoals = Thm.cprems_of
end

datatype 's goal_cluster_state_base = Goal_Cluster_State of 's
type goal_cluster_state_content = {state : Goal_Cluster_State.t}
type goal_cluster_state = goal_cluster_state_content goal_cluster_state_base

fun goal_cluster_state state = Goal_Cluster_State {state = state}
fun get_goal_cluster_state_state (Goal_Cluster_State {state}) = state
fun map_goal_cluster_state_state f (Goal_Cluster_State {state}) =
  Goal_Cluster_State {state = f state}

datatype 'g goal_cluster_base = Goal_Cluster of 'g
type 'prio_tac_ret goal_cluster_content = {state : goal_cluster_state, prio_tac_ret : 'prio_tac_ret}
type 'prio_tac_ret goal_cluster = ('prio_tac_ret goal_cluster_content) goal_cluster_base

fun goal_cluster state prio_tac_ret = Goal_Cluster {state = state, prio_tac_ret = prio_tac_ret}
fun dest_goal_cluster (Goal_Cluster goal_cluster) = goal_cluster
fun get_goal_cluster_state (Goal_Cluster {state, ...} : 'prio_tac_ret goal_cluster) = state
fun get_goal_cluster_prio_tac_ret (Goal_Cluster {prio_tac_ret, ...}) = prio_tac_ret
fun map_goal_cluster_state f (Goal_Cluster {state, prio_tac_ret}) =
  Goal_Cluster {state = f state, prio_tac_ret = prio_tac_ret}
fun map_goal_cluster_prio_tac_ret f (Goal_Cluster {state, prio_tac_ret}) =
  Goal_Cluster {state = state, prio_tac_ret = f prio_tac_ret}

type ('prio_tac_ret, 'tns) goal_node = ('prio_tac_ret goal_cluster, 'tns) Node.node
type ('prio_tac_ret, 'tns) goal_nodes = ('prio_tac_ret, 'tns) goal_node List.t *)


end
