(*  Title:      Zippy/zippy_prover.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER =
sig
  include ZIPPY_PROVER_BASE

  (* containers *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val list_container_zippers{i} : (@{ParaT_args} @{AllT_args} Z{i}.zipper, @{AllT_args} Z{i}.zipper list) cat\<close>\<close>

  (* lenses *)
  (** Z1 **)
  val set_gcluster_list : (@{ParaT_args} gcluster, @{AllT_args} gcd_more) cat -> gcluster list ->
    (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move

  (** Z5 **)
  val set_gclusters : @{AllT_args} gcsd_more -> gclusters ->
    (@{ParaT_args} @{AllT_args} Z5.zipper) hom_move

  (* nodes *)
  (** Z1 **)
  val move_cpos : GCS.cluster_pos -> (@{ParaT_args} @{AllT_args} Z1.zipper, @{AllT_args} Z2.zipper) cat

  (** Z2 **)
  val mk_gcluster_nodes : (@{ParaT_args} gcluster, @{AllT_args} gcd_more) cat ->
    (@{ParaT_args} gcluster list, @{AllT_args} ZCORE.N2.node list) cat

  val cons_move_actionc : @{AllT_args} ZCORE.N3.node ->
    (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} Z3.zipper) cat

  (** Z3 **)
  val cons_move_action : @{AllT_args} ZCORE.N4.node ->
    (@{ParaT_args} @{AllT_args} Z3.zipper, @{AllT_args} Z4.zipper) cat

  (** Z4 **)
  val cons_move_actiona : @{AllT_args} ZCORE.N5.node ->
    (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} Z5.zipper) cat

  (* copy *)
  (** make copy **)
  val copy_cpfocus :
    (focus -> @{AllT_args} Z3.zipper ->
      (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} Z1.zipper) cat) ->
    (GCS.cluster_pos * focus) -> @{AllT_args} Z3.zipper ->
    (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move

  val copy_cpfocuss :
    (focus -> @{AllT_args} Z3.zipper ->
      (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} Z1.zipper) cat) ->
    (GCS.cluster_pos * focus) list -> @{AllT_args} Z3.zipper ->
    (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move

  val copy_update_focus :
    (focus -> @{AllT_args} Z3.zipper ->
      (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} Z1.zipper) cat) ->
    focus -> @{AllT_args} copy

  (* actions *)
  val cons_move_result_actiona_node : @{AllT_args} rdd_more -> prio -> result ->
    (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} Z5.zipper) cat

  val update_result_fold_parents : @{AllT_args} rdd_more -> @{AllT_args} gcsd_more ->
    (@{ParaT_args} gcluster, @{AllT_args} gcd_more) cat ->
    (* get zippers *)
    (@{ParaT_args} @{AllT_args} Z3.zipper, 'zs) cat ->
    (* foldM *)
    ((@{AllT_args} Z3.zipper -> (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move) ->
      'zs -> (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move) ->
    (copy_update_data -> (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move) ->
    prio -> result -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} Z1.zipper) cat

  val update_result : @{AllT_args} rdd_more -> @{AllT_args} gcsd_more ->
    (@{ParaT_args} gcluster, @{AllT_args} gcd_more) cat ->
    (copy_update_data -> (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move) ->
    prio -> result -> (@{ParaT_args} @{AllT_args} Z4.zipper, @{AllT_args} Z1.zipper) cat

  (** action from presult **)
  val update_result_tail_presults : @{AllT_args} rdd_more -> @{AllT_args} gcsd_more ->
    (@{ParaT_args} gcluster, @{AllT_args} gcd_more) cat ->
    (copy_update_data -> (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move) ->
    (prio -> @{AllT_args} presults -> (@{ParaT_args} @{AllT_args} Z4.zipper) hom_move) ->
    result * @{AllT_args} presults -> @{AllT_args} action

  val cons_move_single_presults_action : @{AllT_args} rdd_more -> @{AllT_args} gcsd_more ->
    (@{ParaT_args} gcluster, @{AllT_args} gcd_more) cat ->
    @{AllT_args} cd_more -> @{AllT_args} action_fd_more ->
    (focus -> (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} presults) cat) ->
    (focus -> copy_update_data -> (@{ParaT_args} @{AllT_args} Z1.zipper) hom_move) ->
    focus -> (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} Z4.zipper) cat

  (* initialisation *)
  val init_state : (@{ParaT_args} @{AllT_args} ZCORE.N1.node, @{AllT_args} Z1.ZM.container) cat ->
    @{AllT_args} gcsd_more -> (@{ParaT_args} gcluster, @{AllT_args} gcd_more) cat ->
    (@{ParaT_args} GCS.state, (focus -> (int * focus) list) * @{AllT_args} Z1.zipper) cat

  (* finish *)
  val finish_gclusters_fold : (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} Z1.zipper list) cat ->
    ((@{ParaT_args} @{AllT_args} Z1.zipper, thm Seq.seq) cat ->
      @{AllT_args} Z1.zipper list -> (@{ParaT_args} thm Seq.seq) hom_move) ->
    Proof.context -> (@{ParaT_args} @{AllT_args} Z1.zipper, thm Seq.seq) cat

  val finish_gclusters_oldest_first : Proof.context ->
    (@{ParaT_args} @{AllT_args} Z1.zipper, thm Seq.seq) cat
end

functor Zippy_Prover(Z : ZIPPY_PROVER_BASE) : ZIPPY_PROVER =
struct

open Z

(* misc *)
fun seq_snoc sq x = Seq.append sq (Seq.single x)

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z1)
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
  structure C = \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(A)
  structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)
  structure LT = \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(M))
  structure LF = \<^eval>\<open>sfx_ParaT_nargs "Foldable_Monad"\<close>(
    structure F = \<^eval>\<open>sfx_ParaT_nargs "List_Foldable_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Foldable"\<close>)
    structure M = M)
  open SC M A
in

(*TODO: generalise enumeration of zipper; double check foldlM or foldrM*)
(* containers *)
structure EU = \<^eval>\<open>sfx_ParaT_nargs "Enumerable_Util"\<close>(structure CO = CO)

fun list_container_zippers unzip first next = unzip >>> EU.list first next
(*invariant: operations add new node to the front of the lists*)
val fold_newest_first = LF.foldlM
val fold_oldest_first = LF.foldrM

(*TODO: add more enumerations*)
\<^imap>\<open>\<open>{i}\<close> => \<open>
val first{i} = Z{i}.ZM.Zip.move
val next{i} = Z{i}.ZM.Down.move
fun list_container_zippers{i} x = x |> (list_container_zippers Z{i}.ZM.Unzip.move first{i} next{i})\<close>\<close>

(* lenses *)
fun set_next_safe next n z = LK.set_safe next (pure n, z)
fun set_next next = next |> L.set |> curry

fun gen_cons_node next n =
  AE.catch' ((next |> map_monad |> curry) (arr (cons n))) (set_next next (pure [n]))
fun gen_cons_move_node next down n = gen_cons_node next n >>> down

(* lenses and nodes *)
(** Z1 **)
fun move_cpos cpos = Down1.move >>> C.repeatn cpos next2

(** Z2 **)
fun mk_gcluster_nodes mk_m = LT.traverse (fn gc => mk_m gc >>= (fn m => mk_gcluster_node m gc))
fun set_gcluster_list mk_m gcs z = mk_gcluster_nodes mk_m gcs
  >>= (fn n => set_next_safe (gclusters_next ()) n z)

fun cons_move_actionc x = x |> gen_cons_move_node (gcluster_next ()) Down2.move

(** Z3 **)
fun cons_move_action x = x |> gen_cons_move_node (actionc_next ()) Down3.move

(** Z4 **)
fun cons_move_actiona x = x |> gen_cons_move_node (action_next ()) Down4.move

(** Z5 **)
fun set_gclusters m gcs z = mk_gclusters_node m gcs
  >>= (fn n => set_next_safe (actiona_next ()) n z)

(* copy *)
(** make copy **)
fun copy_cpfocus init_copy = gen_copy_cpfocus move_cpos init_copy
fun copy_cpfocuss init_copy = gen_copy_cpfocuss (copy_cpfocus init_copy)
fun copy_update_focus init_copy = gen_copy_update_focus (copy_cpfocuss init_copy)

(* actions *)
fun cons_move_result_actiona_node rddm prio rud z =
  mk_result_actiona_node rddm prio rud z
  >>= (fn n => cons_move_actiona n z)

fun update_result_fold_parents rddm gcsdm mk_gcdm get_zippers foldM = gen_update_result_copy_parent_actions
  (fn prio => gen_init_result_update_data (cons_move_result_actiona_node rddm prio)
    (fn gcs => set_gclusters gcsdm gcs >>> Down5.move)
    (fn gcs => set_gcluster_list mk_gcdm gcs))
  (Up1.move >>> Up5.move >>> Up4.move >>> get_zippers)
  (copy_parent_actions foldM)

fun update_result rddm gcsdm mk_gcdm = update_result_fold_parents rddm gcsdm mk_gcdm
  list_container_zippers3 fold_oldest_first

(** action from presult **)
fun update_result_tail_presults rddm gcsdm mk_gcdm update_child = gen_update_result_tail_presults
  (fn p => fn r => update_result rddm gcsdm mk_gcdm update_child p r >>> Up1.move >>> Up5.move)

fun gen_cons_move_single_presults_action_copy cdm afdm mk_presults update_result_tail_presults copy focus
  z =
  mk_presults z
  >>= (fn presults => mk_actionc_node cdm copy
  >>= (fn n => cons_move_actionc n z)
  >>= (fn z => mk_presults_action_node afdm focus init_actiona_num presults
    update_result_tail_presults
  >>= (fn n => cons_move_action n z)))

fun gen_cons_move_single_presults_action cdm afdm mk_presults update_result_tail_presults focus =
  let
    fun init_copy focus _ = AE.try (
      gen_cons_move_single_presults_action cdm afdm mk_presults update_result_tail_presults focus
      >>> Up4.move >>> Up3.move)
      >>> Up2.move
    val copy = copy_update_focus init_copy focus
  in
    gen_cons_move_single_presults_action_copy cdm afdm (mk_presults focus)
      (update_result_tail_presults focus) copy focus
  end

fun cons_move_single_presults_action rddm gcsdm mk_gcdm cdm afdm mk_presults update_child =
  gen_cons_move_single_presults_action cdm afdm mk_presults
    (fn focus => update_result_tail_presults rddm gcsdm mk_gcdm (update_child focus)
      (Library.K update_tail_presults))

(* initialisation *)
fun init_state mk_container gcsdm mk_gcdm state = gen_init_result_update_data
  (fn _ => K ())
  (fn gcs => fn _ => mk_gclusters_node gcsdm gcs >>= mk_container >>= Z1.ZM.Zip.move)
  (set_gcluster_list mk_gcdm)
  (T.RD.result_data (state, ()) |> rpair T.GPU.id |> T.RUD.result_update_data)
  ()

(* finish *)
fun gen_finish_gclusters get_gcluster_list_statesq ctxt =
  AE.catch' get_gcluster_list_statesq (K Seq.empty) &&& L.get (gclusters ())
  >>> arr (fn (gcluster_statesq, gcs) =>
    Seq.maps (fn gcluster_states => GCS.finish_cluster_states ctxt gcluster_states gcs)
      gcluster_statesq
    (*base case: no more subgoals*)
    |> GCS.is_finished gcs ? (fn sq => Seq.cons (GCS.get_state gcs) sq))

fun gen_get_gcluster_list_statesq finish_gcluster_list =
  Down1.move
  >>> list_container_zippers2
  >>> finish_gcluster_list

local
structure LTSM = \<^eval>\<open>sfx_ParaT_nargs "Traversable"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "List_Traversable_Trans"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Identity_Traversable"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Seq_Monad_Trans"\<close>(M))))
in
fun gen_finish_gcluster_list finish_gcluster = LTSM.traverse finish_gcluster
end

fun gen_finish_gcluster list_gclusters_children fold_append finish_gclusters z = z |>
  (AE.catch' list_gclusters_children (K [])
  >>> (fn gcs => fold_append finish_gclusters gcs Seq.empty)
  >>> (fn gcs_statesq => get_gcluster_state z
  >>= arr (seq_snoc gcs_statesq)))

fun finish_gclusters_fold list_gclusters_children fold_append ctxt x = x |>
  gen_finish_gclusters (get_gcluster_list_statesq_fold list_gclusters_children fold_append ctxt) ctxt
and get_gcluster_list_statesq_fold list_gclusters_children fold_append ctxt x = x |>
  gen_get_gcluster_list_statesq (finish_gcluster_list_fold list_gclusters_children fold_append ctxt)
and finish_gcluster_list_fold list_gclusters_children fold_append ctxt x = x |>
  gen_finish_gcluster_list (finish_gcluster_fold list_gclusters_children fold_append ctxt)
and finish_gcluster_fold list_gclusters_children fold_append ctxt x = x |>
  gen_finish_gcluster list_gclusters_children fold_append
    (finish_gclusters_fold list_gclusters_children fold_append ctxt)

fun list_zipper5_gclusters_children x = x |> (Down5.move >>> list_container_zippers1)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and list_zipper{i}_gclusters_children x = x |>
  (Down{i}.move
  >>> list_container_zippers\<^eval>\<open>succ_mod_nzippers {i}\<close>
  >>> LT.traverse (AE.catch'
    list_zipper\<^eval>\<open>succ_mod_nzippers {i}\<close>_gclusters_children (K []))
  >>> arr List.concat)\<close>
where start = 2 and stop = 4\<close>

fun apply_append f x acc = f x >>= arr (Seq.append acc)
fun fold_newest_first_append f = fold_newest_first (apply_append f)
fun fold_oldest_first_append f = fold_oldest_first (apply_append f)

fun finish_gclusters_oldest_first x = x
  |> finish_gclusters_fold list_zipper2_gclusters_children fold_oldest_first_append

end

end

functor Instantiate_Zippy_Prover(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_PROVER
  ) :
    ZIPPY_PROVER
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCOREAZ{i}.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.content\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCOREAZ{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.zipper\<close>
      where start = 2\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.zcontext{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.zcontext{i}
    where type @{AllT_args} ZCORE.pzipper{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.pzipper{i}\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{AllT_args} Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type @{AllT_args} gcsd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.gcsd_more
    where type @{AllT_args} gcd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.gcd_more
    where type @{AllT_args} cd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{AllT_args} action_fd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.action_fd_more
    where type @{AllT_args} rdd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.rdd_more
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{AllT_args} presults = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_Prover_Base(open Base; structure Z = Z)
open Z
end

