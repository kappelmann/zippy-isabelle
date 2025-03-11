(*  Title:      HOCLP/gen_zippy_prover.ML
    Author:     Kevin Kappelmann
*)
signature GEN_ZIPPY_PROVER =
sig
  include GEN_ZIPPY_PROVER_BASE

  val exn : 'p1 AE.exn

  (* lenses *)
  structure LK : LENS_KLEISLI_EXCEPTION
  where type ('p1, 'a) K.M.t = ('p1, 'a) M.t
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) L.C.cat
  sharing type LK.lens = L.lens

  val map_monad : ('p1, 't, ('p1, 's) M.t, 'i, ('p1, 'o) M.t) LK.lens ->
    ('p1, 't, 's, 'i, 'o) L.modifier
  val set_no_next : ('p1, 't, ('p1, 'n) M.t, 'i, 'o) L.lens -> ('p1, 'i, 't) cat

  (** Z1 **)
  val get_gclusters_state : (@{ParaT_args}, @{T_args} Z1.zipper, GCS.state) cat
  val is_gclusters_finished : (@{ParaT_args}, @{T_args} Z1.zipper, bool) cat

  (** Z2 **)
  val get_gcluster_state : (@{ParaT_args}, @{T_args} Z2.zipper, GCS.state) cat

  (** Z5 **)
  val node_result_data : unit -> (@{ParaT_args}, @{T_args} ZCORE.N5.node, result_data) L.slens
  val node_result : unit -> (@{ParaT_args}, @{T_args} ZCORE.N5.node, GC.GCS.state) L.slens
  val node_rd_more : unit -> (@{ParaT_args}, @{T_args} ZCORE.N5.node, rd_more) L.slens
  val node_rdd_more : unit -> (@{ParaT_args}, @{T_args} ZCORE.N5.node, @{T_args} rdd_more) L.slens

  val result_data : unit -> (@{ParaT_args}, @{T_args} Z5.zipper, result_data) L.slens
  val result : unit -> (@{ParaT_args}, @{T_args} Z5.zipper, GC.GCS.state) L.slens
  val rd_more : unit -> (@{ParaT_args}, @{T_args} Z5.zipper, rd_more) L.slens
  val rdd_more : unit -> (@{ParaT_args}, @{T_args} Z5.zipper, @{T_args} rdd_more) L.slens

  (* nodes *)
  (** Z1 **)
  val mk_gclusters_node : @{T_args} gcsd_more -> (@{ParaT_args}, gclusters, @{T_args} ZCORE.N1.node) cat

  (** Z2 **)
  val mk_gcluster_node : @{T_args} gcd_more -> (@{ParaT_args}, gcluster, @{T_args} ZCORE.N2.node) cat

  (** Z3 **)
  val mk_actionc_node : @{T_args} cd_more -> (@{ParaT_args}, @{T_args} copy, @{T_args} ZCORE.N3.node) cat

  (** Z4 **)
  val mk_action_node : @{T_args} action_fd_more -> focus -> actiona_num -> @{T_args} presults ->
    (@{ParaT_args}, @{T_args} paction, @{T_args} ZCORE.N4.node) cat

  (** Z5 **)
  val mk_actiona_node : @{T_args} rdd_more -> result_data -> focus -> actiona_num ->
    (@{ParaT_args}, prio, @{T_args} ZCORE.N5.node) cat

  (* copy *)
  (** make copy **)
  val gen_copy_cpfocus :
    (*move to cluster position*)
    (GCS.cluster_pos -> ('p1, 'z1, 'z2) cat) ->
    (*initialise the copy*)
    (focus -> 'z3 -> ('p1, 'z2, 'z4) cat) ->
    (GCS.cluster_pos * focus) -> 'z3 -> ('p1, 'z1, 'z4) cat

  val gen_copy_cpfocuss : (GCS.cluster_pos * focus -> 'z3 -> ('p1, 'z1) hom_move) ->
    (GCS.cluster_pos * focus) list -> 'z3 -> ('p1, 'z1) hom_move

  val gen_copy_update_focus :
    ((GCS.cluster_pos * focus) list -> @{T_args} Z3.zipper ->
      (@{ParaT_args}, @{T_args} Z1.zipper) hom_move) ->
    focus -> @{T_args} copy

  (* presults *)
  val mk_presults_action_node : @{T_args} action_fd_more -> focus -> actiona_num ->
    @{T_args} presults -> (@{ParaT_args},
      (result * @{T_args} presults -> @{T_args} action), @{T_args} ZCORE.N4.node) cat

  val presults_from_tac :
    (@{ParaT_args}, @{T_args} Z4.zipper * result Seq.seq, prio * result Seq.seq) CO.coroutine ->
    rd_more T.zippy_tactic -> (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} presults) cat

  (* actions *)
   val gen_init_result_update_data :
    ('m T.result_update_data -> ('p1, 'z4, 'z5) cat) ->
    (GCS.gclusters -> ('p1, 'z5, 'z1) cat) ->
    (GC.gcluster list -> ('p1, 'z1, 'z2) cat) ->
    'm T.result_update_data -> ('p1, 'z4, copy_update_data * 'z2) cat

  val mk_result_actiona_node : @{T_args} rdd_more -> prio -> result ->
    (@{ParaT_args}, @{T_args} Z4.zipper, @{T_args} ZCORE.N5.node) cat

  (** action priorities **)
  val update_prio_co : ('z -> 'p -> 'p) -> 'p -> ('p1, 'z * 'sq, 'p * 'sq) CO.coroutine

end

functor Gen_Zippy_Prover(Z : GEN_ZIPPY_PROVER_BASE) : GEN_ZIPPY_PROVER =
struct

open Z.ZCORE Z

val exn = ()

local structure SC = Semi_Category(Z); structure M = Monad(M); structure A = Kleisli_Arrow(M);
  open SC M A
in

(* lenses *)
structure LK = Lens_Kleisli_Exception(
  structure AE = struct open AE structure K = A.K end
  structure L = L)

fun map_monad l = LK.lens_monad l |> L.modify

fun set_next next = next |> L.set |> curry
fun set_no_next next = set_next next (no_next exn)
fun rpair_no_next z = (z, no_next exn)

(** Z1 **)
fun get_gclusters x = x |> (L.get (gclusters ()))
fun get_gclusters_state x = x |> (get_gclusters >>> arr GCS.get_state)
fun is_gclusters_finished x = x |> (get_gclusters >>> arr GCS.is_finished)

(** Z2 **)
fun get_gcluster_state x = x |> (L.get (gcluster ()) >>> arr GC.get_state)

(** Z5 **)
fun node_result_data _ = node_actiona_fd_more () \> RDD.result_data
fun node_result _ = node_result_data () \> RD.result
fun node_rd_more _ = node_result_data () \> RD.more
fun node_rdd_more _ = node_actiona_fd_more () \> RDD.more

fun result_data _ = actiona_node () \> node_result_data
fun result _ = actiona_node () \> node_result
fun rd_more _ = actiona_node () \> node_rd_more
fun rdd_more _ = actiona_node () \> node_rdd_more

(* nodes *)
(** Z1 **)
fun mk_gclusters_node m = (rpair m #> GCSD.gclusters_data)
  >>> (rpair_no_next #> N1.node)

(** Z2 **)
fun mk_gcluster_node m = (rpair m #> GCD.gcluster_data)
  >>> (rpair_no_next #> N2.node)

(** Z3 **)
fun mk_actionc_node m = (rpair m #> CD.copy_data)
  >>> (rpair_no_next #> N3.node)

(** Z4 **)
fun mk_action_node m focus actiona_num presults paction =
  FD.focus_data (focus, m)
  >>= (pair actiona_num #> AND.actiona_num_data)
  >>= (pair presults #> PRD.presults_data)
  >>= (pair paction #> PAD.paction_data)
  >>= (rpair_no_next #> N4.node)

(** Z5 **)
fun mk_actiona_node m result_data focus actiona_num prio =
  RDD.result_data_data (result_data, m)
  >>= (pair focus #> FD.focus_data)
  >>= (pair actiona_num #> AND.actiona_num_data)
  >>= (pair prio #> PD.prio_data)
  >>= (rpair_no_next #> N5.node)

(* copy *)
(** make copy **)
fun gen_copy_cpfocus move_cpos init_copy (cpos, focus) zipper3 =
  move_cpos cpos >>> init_copy focus zipper3

local
structure LF = Foldable_Monad(structure F = List_Foldable_Trans(Identity_Foldable); structure M = M)
in
fun gen_copy_cpfocuss copy_cpfocus cpfs x =
  LF.foldlM (fn cpf => AE.try (copy_cpfocus cpf x)) cpfs
end
fun gen_copy_update_focus copy_cpfocuss focus = (fn cud => copy_cpfocuss (cud focus)) |> mk_copy

(* presults *)
fun mk_presults_action_node m focus actiona_num presults update_result_tail_presults =
  mk_action_node m focus actiona_num presults
    (paction_from_presults exn update_result_tail_presults)

fun presults_from_tac mk_prio_sq_c tac =
  get_gcluster_state >>> arr (presults_from_tac_state exn mk_prio_sq_c tac)

(* actions *)
fun gen_init_result_update_data add_move_actiona_node set_gcs set_gc_list rud =
  let val (cud, (gcs, gc_list)) = T.init_result_update_data rud
  in add_move_actiona_node rud >>> set_gcs gcs >>> set_gc_list gc_list >>> arr (pair cud) end

fun mk_result_actiona_node rddm prio rud =
  L.get (action_actiona_num ()) &&& L.get (action_focus ())
  >>> (fn (actiona_num, focus) =>
    mk_actiona_node rddm (T.RUD.get_result rud) focus actiona_num prio)

(** action priorities **)
fun update_prio_co update_prio p =
  arr (fn (z, sq) =>
    let val p = update_prio z p
    in ((p, sq), update_prio_co update_prio p) end)
  |> CO.coroutine

end

end

functor Instantiate_Gen_Zippy_Prover(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : GEN_ZIPPY_PROVER
  ) :
    GEN_ZIPPY_PROVER
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCORE.A.Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZM.container
    where type @{T_args} ZCORE.A.Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.content
    where type @{T_args} ZCORE.A.Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.zcontext
    where type @{T_args} ZCORE.A.Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.zipper\<close>\<close>
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
structure Z = Instantiate_Gen_Zippy_Prover_Base(open Base; structure Z = Z)
open Z
end
