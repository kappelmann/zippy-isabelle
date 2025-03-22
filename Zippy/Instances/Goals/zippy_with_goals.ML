(*  Title:      Zippy/zippy_with_goals.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_WITH_GOALS =
sig
  include ZIPPY_WITH_GOALS_BASE

  (* lenses *)
  (** Z1 (goal clusters) **)
  val gclusters_node : unit -> (@{ParaT_args} @{AllT_args} Z1.zipper, @{AllT_args} ZCORE.N1.node) L.slens

  val node_gclusters : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N1.node, gclusters) L.slens
  val node_gcsd_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N1.node, @{AllT_args} gcsd_more) L.slens

  val gclusters : unit -> (@{ParaT_args} @{AllT_args} Z1.zipper, gclusters) L.slens
  val gcsd_more : unit -> (@{ParaT_args} @{AllT_args} Z1.zipper, @{AllT_args} gcsd_more) L.slens
  val gclusters_next : unit -> (@{ParaT_args} @{AllT_args} Z1.zipper, @{AllT_args} ZCORE.N1.next) L.slens

  (** Z2 (goal cluster) **)
  val gcluster_node : unit -> (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} ZCORE.N2.node) L.slens

  val node_gcluster : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N2.node, gcluster) L.slens
  val node_gcd_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N2.node, @{AllT_args} gcd_more) L.slens

  val gcluster : unit -> (@{ParaT_args} @{AllT_args} Z2.zipper, gcluster) L.slens
  val gcd_more : unit -> (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} gcd_more) L.slens
  val gcluster_next : unit -> (@{ParaT_args} @{AllT_args} Z2.zipper, @{AllT_args} ZCORE.N2.next) L.slens

  (** Z4 **)
  val action_node_focus : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N4.node, focus) L.slens
  val node_action_fd_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N4.node,
    @{AllT_args} action_fd_more) L.slens

  val action_focus : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper, focus) L.slens
  val action_fd_more : unit -> (@{ParaT_args} @{AllT_args} Z4.zipper,
    @{AllT_args} action_fd_more) L.slens

  (** Z5 **)
  val actiona_node_focus : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N5.node, focus) L.slens
  val node_actiona_fd_more : unit -> (@{ParaT_args} @{AllT_args} ZCORE.N5.node,
    @{AllT_args} actiona_fd_more) L.slens

  val actiona_focus : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper, focus) L.slens
  val actiona_fd_more : unit -> (@{ParaT_args} @{AllT_args} Z5.zipper,
    @{AllT_args} actiona_fd_more) L.slens

end

functor Zippy_With_Goals(
    structure Z : ZIPPY_WITH_GOALS_BASE
  ) : ZIPPY_WITH_GOALS =
struct

open Z.ZCORE Z

(* lenses *)
(** Z1 **)
fun gclusters_node _ = Z1.ZO.content () \> zcore_content1

val node_gcsd = N1.content
fun node_gclusters _ = node_gcsd () \> GCSD.gclusters
fun node_gcsd_more _ = node_gcsd () \> GCSD.more

fun gclusters _ = gclusters_node () \> node_gclusters
fun gcsd_more _ = gclusters_node () \> node_gcsd_more
fun gclusters_next _ = gclusters_node () \> N1.next

(** Z2 **)
fun gcluster_node _ = Z2.ZO.content () \> zcore_content2

val node_gcd = N2.content
fun node_gcluster _ = node_gcd () \> GCD.gcluster
fun node_gcd_more _ = node_gcd () \> GCD.more

fun gcluster _ = gcluster_node () \> node_gcluster
fun gcd_more _ = gcluster_node () \> node_gcd_more
fun gcluster_next _ = gcluster_node () \> N2.next

(** Z4 **)
fun action_node_focus _ = node_action_and_more () \> FD.focus
fun node_action_fd_more _ = node_action_and_more () \> FD.more

fun action_focus _ = action_node () \> action_node_focus
fun action_fd_more _ = action_node () \> node_action_fd_more

(** Z5 **)
fun actiona_node_focus _ = node_actiona_and_more () \> FD.focus
fun node_actiona_fd_more _ = node_actiona_and_more () \> FD.more

fun actiona_focus _ = actiona_node () \> actiona_node_focus
fun actiona_fd_more _ = actiona_node () \> node_actiona_fd_more

end

functor Instantiate_Zippy_With_Goals(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_GOALS
  ) :
    ZIPPY_WITH_GOALS
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.A.Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZM.container
    where type @{AllT_args} ZCORE.A.Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.content
    where type @{AllT_args} ZCORE.A.Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZO.zcontext
    where type @{AllT_args} ZCORE.A.Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.zipper\<close>\<close>
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
    where type @{AllT_args} actiona_fd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.actiona_fd_more
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{AllT_args} presults = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_With_Goals_Base(open Base; structure Z = Z)
open Z
end
