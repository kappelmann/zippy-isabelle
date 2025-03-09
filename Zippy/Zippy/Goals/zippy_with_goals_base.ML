(*  Title:      HOCLP/zippy_with_goals_base.ML
    Author:     Kevin Kappelmann

Zippy with goals.
*)
signature ZIPPY_WITH_GOALS_BASE =
sig
  type gclusters
  type gcluster
  type focus

  structure GCSD : KLEISLI_ZIPPY_GCLUSTERS_DATA
  type @{T_args} gcsd_more
  structure GCD : ZIPPY_GCLUSTER_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
  sharing type GCD.L.lens = GCSD.L.lens
  type @{T_args} gcd_more
  structure FD : ZIPPY_FOCUS_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
  sharing type FD.L.lens = GCSD.L.lens
  type @{T_args} action_fd_more
  type @{T_args} actiona_fd_more

  include ZIPPY_WITH_PRESULTS
  where type @{T_args} ZCORE.N1.content = (gclusters, @{T_args} gcsd_more) GCSD.gclusters_data
  where type @{T_args} ZCORE.N2.content = (gcluster, @{T_args} gcd_more) GCD.gcluster_data
  where type @{T_args} action_and_more = (focus, @{T_args} action_fd_more) FD.focus_data
  where type @{T_args} actiona_and_more = (focus, @{T_args} actiona_fd_more) FD.focus_data
  where type ('p1, 'a) M.t = ('p1, 'a) GCSD.K.M.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) GCSD.L.lens
end

functor Zippy_With_Goals_Base(
    type gclusters
    type gcluster
    type focus

    structure GCSD : KLEISLI_ZIPPY_GCLUSTERS_DATA
    type @{T_args} gcsd_more
    structure GCD : ZIPPY_GCLUSTER_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
    sharing type GCD.L.lens = GCSD.L.lens
    type @{T_args} gcd_more
    structure FD : ZIPPY_FOCUS_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) GCSD.L.C.cat
    sharing type FD.L.lens = GCSD.L.lens
    type @{T_args} action_fd_more
    type @{T_args} actiona_fd_more

    structure Z : ZIPPY_WITH_PRESULTS
    where type @{T_args} ZCORE.N1.content = @{PolyT_arg 0}
    where type @{T_args} ZCORE.N2.content = @{PolyT_arg 1}
    where type @{T_args} action_and_more = @{PolyT_arg 3}
    where type @{T_args} actiona_and_more = @{PolyT_arg 4}
    where type ('p1, 'a) M.t = ('p1, 'a) GCSD.K.M.t
    where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) GCSD.L.lens
  ) : ZIPPY_WITH_GOALS_BASE =
struct

type gclusters = gclusters
type gcluster = gcluster
type focus = focus

structure GCSD = GCSD
type @{T_args} gcsd_more = @{T_args} gcsd_more
structure GCD = GCD
type @{T_args} gcd_more = @{T_args} gcd_more
structure FD = FD
type @{T_args} action_fd_more = @{T_args} action_fd_more
type @{T_args} actiona_fd_more = @{T_args} actiona_fd_more

open Z

structure Z = Instantiate_Zippy_With_PResults(
  \<^imap>\<open>\<open>{i}\<close> =>
  \<open>type @{T_args} inst{i} = @{PolyT_arg \<open>{i} - 1\<close>}\<close>\<close>
  type @{T_args} inst1 = (gclusters, @{T_args} gcsd_more) GCSD.gclusters_data
  type @{T_args} inst2 = (gcluster, @{T_args} gcd_more) GCD.gcluster_data
  type @{T_args} inst4 = (focus, @{T_args} action_fd_more) FD.focus_data
  type @{T_args} inst5 = (focus, @{T_args} actiona_fd_more) FD.focus_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_Goals_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_GOALS_BASE
  ) :
    ZIPPY_WITH_GOALS_BASE
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
structure Z = Instantiate_Zippy_With_PResults(open Base; structure Z = Z)
open Z
end
