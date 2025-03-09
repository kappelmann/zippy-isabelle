(*  Title:      HOCLP/zippy_prover_instance.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_INSTANCE =
sig
  include ZIPPY_PROVER_INSTANCE_BASE

  (* lenses *)
  (** Z3 **)
  val node_action_cluster_metadata : unit -> (@{ParaT_args}, @{T_args} ZCORE.N3.node, ACMD.metadata) L.slens
  val action_cluster_metadata : unit -> (@{ParaT_args}, @{T_args} Z3.zipper, ACMD.metadata) L.slens

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

  (* actions *)
  (** action from presult **)
  val cons_move_single_presults_action' : @{T_args} cd_more -> @{T_args} action_fd_more ->
    (focus -> (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} presults) cat) -> focus ->
    (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} Z4.zipper) cat

end

functor Zippy_Prover_Instance(Z : ZIPPY_PROVER_INSTANCE_BASE) : ZIPPY_PROVER_INSTANCE =
struct

open Z

(* lenses *)
(** Z3 **)
fun node_action_cluster_metadata _ = node_cd_more () \> MDD.metadata
fun action_cluster_metadata _ = actionc_node () \> node_action_cluster_metadata

(** Z4 **)
fun node_action_metadata _ = node_action_fd_more () \> MDD.metadata
fun action_metadata _ = action_node () \> node_action_metadata

(* lenses *)
(** Z5 **)
val node_result_metadata = node_rd_more
fun result_metadata _ = actiona_node () \> node_result_metadata

local
  structure SC = Semi_Category(Z); structure M = Monad(K.M)
  open SC M
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

fun cons_move_single_presults_action' x = x |>
  cons_move_single_presults_action mk_rdd_more mk_gcsd_more mk_gcd_more

fun up4 x = x |>
  (AE.repeat (Up4.move >>> Up3.move >>> Up2.move >>> Up1.move >>> Up5.move)
  >>> Up4.move >>> Up3.move >>> Up2.move)

local
structure Zippy_DFS = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable_Alternating_Zippers"\<close>(
  structure Base = struct structure AE = AE end
  structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Rotate_Alternating_Zippers"\<close>(
    \<^eval>\<open>T_Args.suffix_Poly_nargs "Rotate_Alternating_Zippers"\<close>(
    \<^eval>\<open>T_Args.suffix_Poly_nargs "Rotate_Alternating_Zippers"\<close>(Z)))
  structure E1 = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable" ^ "_Zipper_Moves"\<close>(
    open Base; structure Z = Z.Z1.ZM)
  structure E2 = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable" ^ "_Zipper_Moves"\<close>(
    open Base; structure Z = Z.Z2.ZM)
  structure E3 = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable" ^ "_Zipper_Moves"\<close>(
    open Base; structure Z = Z.Z3.ZM)
  structure E4 = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable" ^ "_Zipper_Moves"\<close>(
    open Base; structure Z = Z.Z4.ZM)
  structure E5 = \<^eval>\<open>T_Args.suffix_Poly_nargs "DFS_Postorder_Enumerable" ^ "_Zipper_Moves"\<close>(
    open Base; structure Z = Z.Z5.ZM)
  structure AE = AE)
in
fun fold_max_paction_dfs x = x |> (fold_pactions_max P.ord (Z.id ()) Zippy_DFS.next)
fun fold_run_max_paction_dfs x = x |> (fold_max_paction_dfs >>> fold_pactions_run_single_res)
end

end

end

functor Instantiate_Zippy_Prover_Instance(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_PROVER_INSTANCE
  ) :
    ZIPPY_PROVER_INSTANCE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.content\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} ZCOREAZ{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.ZCOREAZ{i}.zipper\<close>
      where start = 2\<close>
    where type ('p1, 'a) MS.mt = ('p1, 'a) Z.MS.mt
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
    where type @{T_args} paction = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{T_args} copy = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{T_args} presults = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_Prover_Instance_Base(open Base; structure Z = Z)
open Z
end

