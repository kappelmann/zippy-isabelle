(*  Title:      HOCLP/zippy_with_goals_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_WITH_GOALS_UTIL =
sig
  include ZIPPY_WITH_GOALS

  (* lenses *)
  (** Z1 (goal clusters) **)
  val gclusters_node : unit -> (@{ParaT_args}, @{T_args} Z1.zipper, @{T_args} N1.node) L.slens

  val node_gclusters : unit -> (@{ParaT_args}, @{T_args} N1.node, gclusters) L.slens
  val node_gcsd_more : unit -> (@{ParaT_args}, @{T_args} N1.node, @{T_args} gcsd_more) L.slens

  val gclusters : unit -> (@{ParaT_args}, @{T_args} Z1.zipper, gclusters) L.slens
  val gcsd_more : unit -> (@{ParaT_args}, @{T_args} Z1.zipper, @{T_args} gcsd_more) L.slens
  val gclusters_next : unit -> (@{ParaT_args}, @{T_args} Z1.zipper, @{T_args} N1.next) L.slens

  (** Z2 (goal cluster) **)
  val gcluster_node : unit -> (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} N2.node) L.slens

  val node_gcluster : unit -> (@{ParaT_args}, @{T_args} N2.node, gcluster) L.slens
  val node_gcd_more : unit -> (@{ParaT_args}, @{T_args} N2.node, @{T_args} gcd_more) L.slens

  val gcluster : unit -> (@{ParaT_args}, @{T_args} Z2.zipper, gcluster) L.slens
  val gcd_more : unit -> (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} gcd_more) L.slens
  val gcluster_next : unit -> (@{ParaT_args}, @{T_args} Z2.zipper, @{T_args} N2.next) L.slens

  (** Z4 **)
  val action_node_focus : unit -> (@{ParaT_args}, @{T_args} N4.node, focus) L.slens
  val node_action_fd_more : unit -> (@{ParaT_args}, @{T_args} N4.node,
    @{T_args} action_fd_more) L.slens

  val action_focus : unit -> (@{ParaT_args}, @{T_args} Z4.zipper, focus) L.slens
  val action_fd_more : unit -> (@{ParaT_args}, @{T_args} Z4.zipper,
    @{T_args} action_fd_more) L.slens

  (** Z5 **)
  val actiona_node_focus : unit -> (@{ParaT_args}, @{T_args} N5.node, focus) L.slens
  val node_actiona_fd_more : unit -> (@{ParaT_args}, @{T_args} N5.node,
    @{T_args} actiona_fd_more) L.slens

  val actiona_focus : unit -> (@{ParaT_args}, @{T_args} Z5.zipper, focus) L.slens
  val actiona_fd_more : unit -> (@{ParaT_args}, @{T_args} Z5.zipper,
    @{T_args} actiona_fd_more) L.slens

end

functor Zippy_With_Goals_Util(
    structure Z : ZIPPY_WITH_GOALS
  ) : ZIPPY_WITH_GOALS_UTIL =
struct

open Z

(* lenses *)
(** Z1 **)
val gclusters_node = Z1.ZO.content

val node_gcsd = N1.content
fun node_gclusters _ = node_gcsd () \> GCSD.gclusters
fun node_gcsd_more _ = node_gcsd () \> GCSD.more

fun gclusters _ = gclusters_node () \> node_gclusters
fun gcsd_more _ = gclusters_node () \> node_gcsd_more
fun gclusters_next _ = gclusters_node () \> N1.next

(** Z2 **)
val gcluster_node = Z2.ZO.content

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

functor Instantiate_Zippy_With_Goals_Util(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_GOALS_UTIL
  ) :
    ZIPPY_WITH_GOALS
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} A.Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZM.container
    where type @{T_args} A.Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.content
    where type @{T_args} A.Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.zcontext
    where type @{T_args} A.Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.zipper\<close>\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} zcontext{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.zcontext{i}
    where type @{T_args} pzipper{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.pzipper{i}\<close>\<close>
    where type @{T_args} gcsd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.gcsd_more
    where type @{T_args} gcd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.gcd_more
    where type @{T_args} cd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{T_args} action_fd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.action_fd_more
    where type @{T_args} actiona_fd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.actiona_fd_more
    where type @{T_args} paction = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{T_args} copy = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{T_args} presults = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_With_Goals(open Base; structure Z = Z)
open Z
end
