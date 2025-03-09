(*  Title:      HOCLP/zippy_prover.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER =
sig
  include ZIPPY_PROVER_BASE

  (* containers *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val list_container_zippers{i} : (@{ParaT_args}, @{T_args} Z{i}.zipper, @{T_args} Z{i}.zipper list) cat\<close>\<close>

  (* lenses *)
  (** Z1 **)
  val set_gcluster_list : (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat -> gcluster list ->
    (@{ParaT_args}, @{T_args} Z1.zipper) hom_move

  (** Z5 **)
  val set_gclusters : @{T_args} gcsd_more -> gclusters ->
    (@{ParaT_args}, @{T_args} Z5.zipper) hom_move

  (* nodes *)
  (** Z1 **)
  val move_cpos : GCS.cluster_pos -> (@{ParaT_args}, @{T_args} Z1.zipper, @{T_args} Z2.zipper) cat

  (** Z2 **)
  val mk_gcluster_nodes : (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat ->
    (@{ParaT_args}, gcluster list, @{T_args} ZCORE.N2.node list) cat

  val cons_move_actionc : @{T_args} ZCORE.N3.node ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z3.zipper) cat

  (** Z3 **)
  val cons_move_action : @{T_args} ZCORE.N4.node ->
    (@{ParaT_args}, @{T_args} Z3.zipper, @{T_args} Z4.zipper) cat

  (** Z4 **)
  val cons_move_actiona : @{T_args} ZCORE.N5.node ->
    (@{ParaT_args}, @{T_args} Z4.zipper, @{T_args} Z5.zipper) cat

  (* copy *)
  (** make copy **)
  val copy_cpfocus :
    (focus -> @{T_args} Z3.zipper ->
      (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z1.zipper) cat) ->
    (GCS.cluster_pos * focus) -> @{T_args} Z3.zipper ->
    (@{ParaT_args}, @{T_args} Z1.zipper) hom_move

  val copy_cpfocuss :
    (focus -> @{T_args} Z3.zipper ->
      (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z1.zipper) cat) ->
    (GCS.cluster_pos * focus) list -> @{T_args} Z3.zipper ->
    (@{ParaT_args}, @{T_args} Z1.zipper) hom_move

  val copy_update_focus :
    (focus -> @{T_args} Z3.zipper ->
      (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z1.zipper) cat) ->
    focus -> @{T_args} copy

  (* actions *)
  val cons_move_result_actiona_node : @{T_args} rdd_more -> prio -> result ->
    (@{ParaT_args}, @{T_args} Z4.zipper, @{T_args} Z5.zipper) cat

  val update_result_fold_parents : @{T_args} rdd_more -> @{T_args} gcsd_more ->
    (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat ->
    (* get zippers *)
    (@{ParaT_args}, @{T_args} Z3.zipper, 'zs) cat ->
    (* foldM *)
    ((@{T_args} Z3.zipper -> (@{ParaT_args}, @{T_args} Z1.zipper) hom_move) ->
      'zs -> (@{ParaT_args}, @{T_args} Z1.zipper) hom_move) ->
    prio -> result -> (@{ParaT_args}, @{T_args} Z4.zipper, @{T_args} Z1.zipper) cat

  val update_result : @{T_args} rdd_more -> @{T_args} gcsd_more ->
    (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat -> prio -> result ->
    (@{ParaT_args}, @{T_args} Z4.zipper, @{T_args} Z1.zipper) cat

  (** action from presult **)
  val update_result_tail_presults : @{T_args} rdd_more -> @{T_args} gcsd_more ->
    (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat ->
    (prio -> @{T_args} presults -> (@{ParaT_args}, @{T_args} Z4.zipper) hom_move) ->
    result * @{T_args} presults -> @{T_args} action

  val cons_move_single_presults_action : @{T_args} rdd_more -> @{T_args} gcsd_more ->
    (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat ->
    @{T_args} cd_more -> @{T_args} action_fd_more ->
    (focus -> (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} presults) cat) -> focus ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z4.zipper) cat

  (* initialisation *)
  val init_state : (@{ParaT_args}, @{T_args} ZCORE.N1.node, @{T_args} Z1.ZM.container) cat ->
    @{T_args} gcsd_more -> (@{ParaT_args}, gcluster, @{T_args} gcd_more) cat ->
    (@{ParaT_args}, GCS.state, (focus -> (int * focus) list) * @{T_args} Z1.zipper) cat

  (* finish *)
  val finish_gclusters_fold : (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z1.zipper list) cat ->
    ((@{ParaT_args}, @{T_args} Z1.zipper, thm Seq.seq) cat ->
      @{T_args} Z1.zipper list -> (@{ParaT_args}, thm Seq.seq) hom_move) ->
    Proof.context -> (@{ParaT_args}, @{T_args} Z1.zipper, thm Seq.seq) cat

  val finish_gclusters_oldest_first : Proof.context ->
    (@{ParaT_args}, @{T_args} Z1.zipper, thm Seq.seq) cat
end

functor Zippy_Prover(Z : ZIPPY_PROVER_BASE) : ZIPPY_PROVER =
struct

open Z

(* misc *)
fun seq_snoc sq x = Seq.append sq (Seq.single x)

local
  structure SC = Semi_Category(Z1); structure M = Monad(M); structure A = Kleisli_Arrow(M)
  structure C = Category(A); structure AA = Kleisli_Arrow_Apply(M)
  structure LT = List_Traversable_Trans(Identity_Traversable(M))
  structure LF = Foldable_Monad(structure F = List_Foldable_Trans(Identity_Foldable); structure M = M)
  open SC M A
in

(*TODO: generalise enumeration of zipper; double check foldlM or foldrM*)
(* containers *)
structure EU = Enumerable_Util(structure CO = CO)

fun list_container_zippers unzip first next = unzip >>> EU.list first next
(*invariant: operations add new node to the front of the lists*)
val fold_newest_first = LF.foldlM
val fold_oldest_first = LF.foldrM

(*FIXME: enums*)
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

fun update_result_fold_parents rddm gcsdm mk_gcdm get_zippers foldM = gen_update_result
  (fn prio => gen_init_result_update_data (cons_move_result_actiona_node rddm prio)
    (fn gcs => set_gclusters gcsdm gcs >>> Down5.move)
    (fn gcs => set_gcluster_list mk_gcdm gcs))
  (Up1.move >>> Up5.move >>> Up4.move >>> get_zippers)
  (copy_parent_actions foldM)

fun update_result rddm gcsdm mk_gcdm = update_result_fold_parents rddm gcsdm mk_gcdm
  list_container_zippers3 fold_oldest_first

(** action from presult **)
fun update_result_tail_presults rddm gcsdm mk_gcdm = gen_update_result_tail_presults
  (fn p => fn r => update_result rddm gcsdm mk_gcdm p r >>> Up1.move >>> Up5.move)

fun gen_cons_move_single_presults_action_copy cdm afdm mk_presults update_result_tail_presults copy focus
  z =
  mk_presults focus z
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
    gen_cons_move_single_presults_action_copy cdm afdm mk_presults update_result_tail_presults copy focus
  end

fun cons_move_single_presults_action rddm gcsdm mk_gcdm cdm afdm mk_presults =
  gen_cons_move_single_presults_action cdm afdm mk_presults
    (update_result_tail_presults rddm gcsdm mk_gcdm (Library.K update_tail_presults))

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

local structure LTSM = Traversable(List_Traversable_Trans(Identity_Traversable(Seq_Monad_Trans(M))))
in
fun gen_finish_gcluster_list finish_gcluster = LTSM.traverse finish_gcluster
end

fun gen_finish_gcluster list_gcluster_children fold_append finish_gclusters z = z |>
  (AE.catch' list_gcluster_children (K [])
  >>> (fn gcs => fold_append finish_gclusters gcs Seq.empty)
  >>> (fn gcs_statesq => get_gcluster_state z
  >>= arr (seq_snoc gcs_statesq)))

fun finish_gclusters_fold list_gcluster_children fold_append ctxt x = x |>
  gen_finish_gclusters (get_gcluster_list_statesq_fold list_gcluster_children fold_append ctxt) ctxt
and get_gcluster_list_statesq_fold list_gcluster_children fold_append ctxt x = x |>
  gen_get_gcluster_list_statesq (finish_gcluster_list_fold list_gcluster_children fold_append ctxt)
and finish_gcluster_list_fold list_gcluster_children fold_append ctxt x = x |>
  gen_finish_gcluster_list (finish_gcluster_fold list_gcluster_children fold_append ctxt)
and finish_gcluster_fold list_gcluster_children fold_append ctxt x = x |>
  gen_finish_gcluster list_gcluster_children fold_append
    (finish_gclusters_fold list_gcluster_children fold_append ctxt)

fun list_zipper5_gcluster_children x = x |> (Down5.move >>> list_container_zippers1)
\<^imap>\<open>\<open>{i}\<close> => \<open>
and list_zipper{i}_gcluster_children x = x |>
  (Down{i}.move
  >>> list_container_zippers\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>
  >>> LT.traverse (AE.catch'
    list_zipper\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>_gcluster_children (K []))
  >>> arr List.concat)\<close>
where start = 2 and stop = 4\<close>

fun apply_append f x acc = f x >>= arr (Seq.append acc)
fun fold_newest_first_append f = fold_newest_first (apply_append f)
fun fold_oldest_first_append f = fold_oldest_first (apply_append f)

fun finish_gclusters_oldest_first x = x
  |> finish_gclusters_fold list_zipper2_gcluster_children fold_oldest_first_append

end

end

functor Instantiate_Zippy_Prover(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_PROVER
  ) :
    ZIPPY_PROVER
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.content\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.zipper\<close>
      where start = 2\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCORE.zcontext{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.zcontext{i}
    where type @{T_args} ZCORE.pzipper{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.pzipper{i}\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZM.container
    where type @{T_args} Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.content
    where type @{T_args} Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZO.zcontext
    where type @{T_args} Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type @{T_args} gcsd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.gcsd_more
    where type @{T_args} gcd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.gcd_more
    where type @{T_args} cd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{T_args} action_fd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.action_fd_more
    where type @{T_args} rdd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.rdd_more
    where type @{T_args} paction = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{T_args} copy = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{T_args} presults = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_Prover_Base(open Base; structure Z = Z)
open Z
end

