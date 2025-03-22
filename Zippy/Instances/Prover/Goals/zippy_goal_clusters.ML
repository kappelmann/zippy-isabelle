(*  Title:      HOCLP/zippy_goal_clusters.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTERS =
sig
  (*counting from 0 as is convention for indexing of datatypes*)
  type cluster_pos = int
  val init_cluster_pos : cluster_pos
  (*counting from 1 as is convention for Isabelle goals*)
  type goal_pos = int
  (*position of a state's goal in the created goal clusters*)
  type gcpos
  val get_gcpos_cluster : gcpos -> cluster_pos
  val get_gcpos_goal : gcpos -> goal_pos
  val mk_gcpos_index : goal_pos list list -> goal_pos -> gcpos

  structure UF : IMPERATIVE_UNION_FIND
  type veclass = term UF.set
  val eq_opt_veclass: 'a UF.set option * 'a UF.set option -> bool
  val init_veclasses : term list -> veclass option list * veclass Termtab.table
  val group_veclasses : veclass option list -> (goal_pos * veclass option) list list
  val build_veclasses : term list -> (goal_pos * veclass option) list list * veclass Termtab.table

  type gclusters
  val pretty_gclusters : Proof.context -> gclusters -> Pretty.T
  (*returns unaltered state*)
  type state = Zippy_Thm_State.state
  val get_state : gclusters -> state
  val get_thm : gclusters -> thm
  (*returns state where clusters are combined with Pure conjunctions (&&&)*)
  val get_clustered_state : gclusters -> state
  val get_cclusters : gclusters -> cterm list
  val get_clusters_goals : gclusters -> term list list
  val get_gcpos_index : gclusters -> goal_pos -> gcpos
  (*returns clusters and associated equivalence classes for the state's goals, including their size*)
  val init : state -> gclusters * (goal_pos list * int) list

  val is_finished : gclusters -> bool

  val finish_cluster_states : Proof.context -> state list -> gclusters -> state Seq.seq
end

functor Zippy_Goal_Clusters(UF : IMPERATIVE_UNION_FIND) : ZIPPY_GOAL_CLUSTERS =
struct

structure UF = UF
structure GU = General_Util
structure TS = Zippy_Thm_State

type cluster_pos = int
val init_cluster_pos = 0
type goal_pos = int
datatype gcpos = GCPos of {cluster : cluster_pos, goal : goal_pos}
fun gcpos cluster goal = GCPos {cluster = cluster, goal = goal}
fun get_gcpos_cluster (GCPos {cluster,...}) = cluster
fun get_gcpos_goal (GCPos {goal,...}) = goal

val out_of_bounds_gcpos = gcpos ~1 ~1

fun mk_gcpos_index veclasses = fold_index (fn (cpos, ps) => fold_index
    (fn (gpos, gpos_in) => General_Util.fun_update (equal gpos_in) (gcpos cpos (GU.succ gpos)))
    ps)
  veclasses (K out_of_bounds_gcpos)

type veclass = term UF.set

fun add_veclass goal vindex =
  let fun merge v (opt_veclass, vindex) =
    let
      val (veclass', vindex) = case Termtab.lookup vindex v of
          NONE => let val veclass = UF.new v
            in (veclass, Termtab.insert (K true) (v, veclass) vindex) end
        | SOME veclass => (veclass, vindex)
      val veclass = opt_veclass
        |> Option.map (fn veclass => (UF.union fst veclass veclass'; veclass))
        |> the_default veclass'
    in (SOME veclass, vindex) end
  in fold_aterms (fn (v as Var _) => merge v | _ => I) goal (NONE, vindex) end
fun init_veclasses goals = fold_map add_veclass goals Termtab.empty

fun eq_opt_veclass (SOME veclass1, SOME veclass2) = UF.eq (veclass1, veclass2)
  | eq_opt_veclass _ = false

val group_veclasses = map_index (apfst GU.succ #> uncurry pair)
  #> Library.partition_eq (apply2 snd #> eq_opt_veclass)
val build_veclasses = init_veclasses #> apfst group_veclasses

fun rearrange_veclasses_state veclasses = Drule.rearrange_prems (flat veclasses |> map GU.pred)
val mk_conj_list_state = fold (fn n => TS.mk_conj n #> Drule.rotate_prems 1)

type state = Zippy_Thm_State.state

datatype gclusters = GClusters of {
    state : state,
    clustered_state : state,
    gcpos_index : goal_pos -> gcpos
  }

fun get_state (GClusters {state,...}) = state
fun get_clustered_state (GClusters {clustered_state,...}) = clustered_state
fun get_gcpos_index (GClusters {gcpos_index,...}) = gcpos_index

val get_thm = get_state #> TS.get_thm

fun pretty_gclusters ctxt gclusters = get_clustered_state gclusters |> TS.pretty ctxt

val get_cclusters = get_clustered_state #> TS.unprotect_prems #> Thm.cprems_of
val get_clusters_goals = get_cclusters #> map (Thm.term_of #> Logic.dest_conjunctions)

fun init state = Thm.prems_of state
  |> build_veclasses
  |> fst
  |> map (fn veclass => fold_map (apfst fst #> apsnd GU.succ |> curry) veclass 0)
  |> `(fn vss =>
    let
      val (veclasses, ss) = split_list vss
      val clustered_state = rearrange_veclasses_state veclasses state
        |> mk_conj_list_state ss
        |> TS.protect_prems
      val gcpos_index = mk_gcpos_index (map fst vss)
    in GClusters {state = state, clustered_state = clustered_state, gcpos_index = gcpos_index} end)

fun is_finished gcluster = get_state gcluster |> TS.is_finished

val finish_cluster_state_tac = Unify_Resolve_Base.unify_resolve_tac
  Higher_Order_Unification.norms Higher_Order_Unification.unify

fun finish_cluster_states ctxt cluster_thms = get_clustered_state
  #> RANGE (map (fn cluster_thm => finish_cluster_state_tac cluster_thm ctxt) cluster_thms) 1

end
