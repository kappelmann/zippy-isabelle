(*  Title:      HOCLP/zippy_prover_instance.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_INSTANCE =
sig
  include ZIPPY_PROVER_INSTANCE_BASE

  (* misc *)
  val with_state : (@{ParaT_args} -> (@{ParaT_args}, 'a, 'b) cat) -> (@{ParaT_args}, 'a, 'b) cat

  (* lenses *)
  (** Z3 **)
  val node_actionc_metadata : unit -> (@{ParaT_args}, @{T_args} ZCORE.N3.node, ACMD.metadata) L.slens
  val actionc_metadata : unit -> (@{ParaT_args}, @{T_args} Z3.zipper, ACMD.metadata) L.slens

  (** Z4 **)
  val node_action_metadata : unit -> (@{ParaT_args}, @{T_args} ZCORE.N4.node, AMD.metadata) L.slens
  val action_metadata : unit -> (@{ParaT_args}, @{T_args} Z4.zipper, AMD.metadata) L.slens

  (** Z5 **)
  val node_result_metadata : unit -> (@{ParaT_args}, @{T_args} ZCORE.N5.node, RMD.metadata) L.slens
  val result_metadata : unit -> (@{ParaT_args}, @{T_args} Z5.zipper, RMD.metadata) L.slens

  (* nodes *)
  (** Z1 **)
  val mk_gcsd_more : @{T_args} gcsd_more
  (** Z2 **)
  val mk_gcd_more : (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat
  (** Z3 **)
  val mk_cd_more : (@{ParaT_args}, ACMD.metadata, @{T_args} cd_more) cat
  (** Z4 **)
  val mk_action_fd_more : (@{ParaT_args}, AMD.metadata, @{T_args} action_fd_more) cat
  (** Z5 **)
  val mk_rdd_more : @{T_args} rdd_more

  (* pretty-printing *)
  (** Z1 **)
  val pretty_gcs : Proof.context -> (@{ParaT_args}, @{T_args} Z1.zipper, Pretty.T) cat
  val pretty_gc : Proof.context -> (@{ParaT_args}, @{T_args} Z2.zipper, Pretty.T) cat
  val pretty_actionc : (@{ParaT_args}, @{T_args} Z3.zipper, Pretty.T) cat
  val pretty_action : (@{ParaT_args}, @{T_args} Z4.zipper, Pretty.T) cat
  val pretty_actiona : (@{ParaT_args}, @{T_args} Z5.zipper, Pretty.T) cat

  (* tactics *)
  (** lifting **)
  val add_all_rmd : RMD.metadata * RMD.metadata -> RMD.metadata

  val lift_every_goals_focus_tac : (GCS.state * GCS.state -> RMD.metadata) ->
    (GCS.goal_pos -> int -> GCS.goal_pos T.GPU.T.target) -> (int -> tactic) -> F.focus ->
    RMD.metadata T.zippy_tactic
  val lift_all_goals_focus_tac : (GCS.state * GCS.state -> RMD.metadata) ->
    (GCS.goal_pos -> int -> GCS.goal_pos T.GPU.T.target) -> (int -> tactic) -> F.focus ->
    RMD.metadata T.zippy_tactic

  (* presults *)
  val presults_from_tac' :
    (@{ParaT_args}, @{T_args} Z4.zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    (F.focus -> RMD.metadata T.zippy_tactic) -> F.focus ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} presults) cat

  (* actions *)
  (** action from presult **)
  val cons_move_single_presults_action' : AMD.metadata ->
    (focus -> (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} presults) cat) -> focus ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z4.zipper) cat

  (** actions from tactics **)
  val cons_move_tac : AMD.metadata ->
    (@{ParaT_args}, @{T_args} Z4.zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    (F.focus -> RMD.metadata T.zippy_tactic) -> F.focus ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z4.zipper) cat

  (** fold and run actions **)
  val fold_max_paction_dfs : (@{ParaT_args},
    @{T_args} Z4.zipper, ((prio * @{T_args} action) * @{T_args} Z4.zipper) AF.res) cat
  val fold_max_paction_dfs_halve_prio_depth : (@{ParaT_args},
    @{T_args} Z4.zipper, ((prio * @{T_args} action) * @{T_args} Z4.zipper) AF.res) cat

  val fold_run_max_paction_dfs : (@{ParaT_args}, @{T_args} Z1.ZM.container, @{T_args} Z4.zipper) cat
  val fold_run_max_paction_dfs_halve_prio_depth : (@{ParaT_args}, @{T_args} Z1.ZM.container,
    @{T_args} Z4.zipper) cat

  val repeat_fold_run_max_paction_dfs : int option ->
    (@{ParaT_args}, @{T_args} Z1.ZM.container) hom_move
  val repeat_fold_run_max_paction_dfs_halve_prio_depth : int option ->
    (@{ParaT_args}, @{T_args} Z1.ZM.container) hom_move

end

functor Zippy_Prover_Instance(Z : ZIPPY_PROVER_INSTANCE_BASE) : ZIPPY_PROVER_INSTANCE =
struct

open Z

(* misc *)
fun with_state f = AS.access (fn (x, s) => f s x)

(* lenses *)
(** Z3 **)
fun node_actionc_metadata _ = node_cd_more () \> MDD.metadata
fun actionc_metadata _ = actionc_node () \> node_actionc_metadata

(** Z4 **)
fun node_action_metadata _ = node_action_fd_more () \> MDD.metadata
fun action_metadata _ = action_node () \> node_action_metadata

(* lenses *)
(** Z5 **)
val node_result_metadata = node_rd_more
fun result_metadata _ = actiona_node () \> node_result_metadata

local
  structure SC = Semi_Category(Z); structure M = Monad(K.M); structure A = Arrow(Z)
  open SC M A
in

(* nodes *)
(** Z1 **)
val mk_gcsd_more = ()
(** Z2 **)
fun mk_gcd_more _ = M.pure ()
(** Z3 **)
fun mk_cd_more m = MDD.metadata_data (m, ())
(** Z4 **)
fun mk_action_fd_more m = MDD.metadata_data (m, ())
(** Z5 **)
val mk_rdd_more = ()

(* pretty-printing *)
local structure Show = SpecCheck_Show_Base
in
(** Z1 **)
fun pretty_gcs ctxt =
  L.get (gclusters ())
  >>> arr (fn gcs => Show.record [
      ("Goal clusters", GCS.pretty_gclusters ctxt gcs)
    ])
(** Z2 **)
fun pretty_gc ctxt =
  L.get (gcluster ())
  >>> arr (fn gc => Show.record [
      ("Goal cluster", GC.pretty_gcluster ctxt gc)
    ])
(** Z3 **)
fun pretty_actionc x = x |>
  (L.get (actionc_metadata ())
  >>> arr (fn acmd => Show.record [
      ("Action cluster", ACMD.pretty_metadata acmd)
    ]))
(** Z4 **)
fun pretty_action x = x |>
  ((L.get (action_metadata ()) &&& L.get (action_focus ()) &&& L.get (action_actiona_num ()))
  >>> arr (fn ((amd, foc), actiona_num) => Show.record [
      ("Action", AMD.pretty_metadata amd),
      ("Focus", F.pretty foc),
      ("Action number", Show.int actiona_num)
    ]))
(** Z5 **)
fun pretty_actiona x = x |>
  (L.get (result_metadata ()) &&& L.get (actiona_focus ()) &&& L.get (actiona_actiona_num ()) &&& L.get (prio ())
  >>> arr (fn (((rmd, foc), actiona_num), prio) => Show.record [
      ("Result", RMD.pretty_metadata rmd),
      ("Focus", F.pretty foc),
      ("Priority", Prio.pretty prio),
      ("Action number", Show.int actiona_num)
    ]))
end

(* tactics *)
(** lifting **)
fun add_all_rmd (rmd1, rmd2) =
  let val progress =
    if forall (equal RMD.promising) (List.map Zippy_Result_Metadata.get_progress [rmd1, rmd2])
    then RMD.promising
    else RMD.unclear
  in Zippy_Result_Metadata.metadata progress end

fun lift_every_goals_focus_tac mk_rmd single_goal_target = T.lift_tac' mk_rmd
  #> T.lift_every_focus_tac T.no_tac add_all_rmd single_goal_target

fun lift_all_goals_focus_tac mk_rmd single_goal_target = T.lift_tac' mk_rmd
  #> T.lift_all_goals_focus_tac T.no_tac add_all_rmd single_goal_target

(* presults *)
fun presults_from_tac' mk_prio_sq_c tac f = presults_from_tac mk_prio_sq_c (tac f)

(* actions *)
(** action from presult **)
local structure ID = Zippy_Identifier
in
fun cons_move_single_presults_action' amdm mk_presults f z =
  AMD.get_id amdm
  >>= (fn id =>
    let
      val acmd_id = ID.combine [id, @{binding "cluster"}]
      val acmd_desc = "Single action cluster for " ^ ID.quoted_string id
    in ACMD.metadata (acmd_id, acmd_desc) end)
  >>= mk_cd_more
  >>= (fn cdm => mk_action_fd_more amdm
  >>= (fn afdm => cons_move_single_presults_action mk_rdd_more mk_gcsd_more mk_gcd_more cdm afdm
    mk_presults f z))
end

(** actions from tactics **)
fun cons_move_tac amd mk_prio_sq_c tac =
  cons_move_single_presults_action' amd (presults_from_tac' mk_prio_sq_c tac)

(** fold and run actions **)
local
structure Zippy_DFS = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable_Alternating_Zippers"\<close>(
  structure Base = struct structure AE = AE end
  structure Z =
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    \<^eval>\<open>T_Args.suffix_Poly_nargs "Rotate_Alternating_Zippers"\<close>(\<close> where stop = 3\<close>
    Z
    \<^imap>\<open>\<open>{i}\<close> => \<open>)\<close> where stop = 3\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure E{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable" ^ "_Zipper_Moves"\<close>(
    open Base; structure Z = Z.Z{i}.ZM)\<close>\<close>
  structure AE = AE)
in
fun gen_fold_max_paction_dfs update_res = fold_pactions_max P.ord update_res Zippy_DFS.next
fun fold_max_paction_dfs x = x |> gen_fold_max_paction_dfs (Z.id ())
fun fold_max_paction_dfs_halve_prio_depth x = x |>
  let fun halve_depth ((p, action), z) =
    L.get (depth4 ()) z >>= arr (fn d => ((funpow d P.halve p, action), z))
  in gen_fold_max_paction_dfs halve_depth end

fun gen_fold_run_paction_dfs fold_paction =
  Zippy_DFS.first3 >>> fold_paction >>> fold_pactions_run_single_res
fun fold_run_max_paction_dfs x = x |> gen_fold_run_paction_dfs fold_max_paction_dfs
fun fold_run_max_paction_dfs_halve_prio_depth x = x |>
  gen_fold_run_paction_dfs fold_max_paction_dfs_halve_prio_depth
end

fun gen_repeat_fold_run_paction fold_run_paction opt_fuel =
  (case opt_fuel of NONE => AE.repeat | SOME n => AE.repeatn_safe n)
  (fold_run_paction  >>> top4 >>> Z1.ZM.Unzip.move)
fun repeat_fold_run_max_paction_dfs opt_fuel =
  gen_repeat_fold_run_paction fold_run_max_paction_dfs opt_fuel
fun repeat_fold_run_max_paction_dfs_halve_prio_depth opt_fuel =
  gen_repeat_fold_run_paction fold_run_max_paction_dfs_halve_prio_depth opt_fuel

end

end
