(*  Title:      Zippy/zippy_with_goals_base.ML
    Author:     Kevin Kappelmann

Zippy with goals.
*)
signature ZIPPY_WITH_GOALS_BASE =
sig
  type gclusters
  type gcluster
  type focus

  structure GCSD : KLEISLI_ZIPPY_GCLUSTERS_DATA
  type @{AllT_args} gcsd_more
  structure GCD : ZIPPY_GCLUSTER_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) GCSD.L.C.cat
  sharing type GCD.L.lens = GCSD.L.lens
  type @{AllT_args} gcd_more
  structure FD : ZIPPY_FOCUS_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) GCSD.L.C.cat
  sharing type FD.L.lens = GCSD.L.lens
  type @{AllT_args} action_fd_more
  type @{AllT_args} actiona_fd_more

  include ZIPPY_WITH_PRESULTS
  where type @{AllT_args} ZCORE.N1.content = (gclusters, @{AllT_args} gcsd_more) GCSD.gclusters_data
  where type @{AllT_args} ZCORE.N2.content = (gcluster, @{AllT_args} gcd_more) GCD.gcluster_data
  where type @{AllT_args} action_and_more = (focus, @{AllT_args} action_fd_more) FD.focus_data
  where type @{AllT_args} actiona_and_more = (focus, @{AllT_args} actiona_fd_more) FD.focus_data
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) GCSD.K.M.t
  where type (@{ParaT_args} 't, 's, 'i, 'o) L.lens = (@{ParaT_args} 't, 's, 'i, 'o) GCSD.L.lens
end

functor Zippy_With_Goals_Base(
    type gclusters
    type gcluster
    type focus

    structure GCSD : KLEISLI_ZIPPY_GCLUSTERS_DATA
    type @{AllT_args} gcsd_more
    structure GCD : ZIPPY_GCLUSTER_DATA
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) GCSD.L.C.cat
    sharing type GCD.L.lens = GCSD.L.lens
    type @{AllT_args} gcd_more
    structure FD : ZIPPY_FOCUS_DATA
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) GCSD.L.C.cat
    sharing type FD.L.lens = GCSD.L.lens
    type @{AllT_args} action_fd_more
    type @{AllT_args} actiona_fd_more

    structure Z : ZIPPY_WITH_PRESULTS
    where type @{AllT_args} ZCORE.N1.content = @{ZipperT_arg 0}
    where type @{AllT_args} ZCORE.N2.content = @{ZipperT_arg 1}
    where type @{AllT_args} action_and_more = @{ZipperT_arg 3}
    where type @{AllT_args} actiona_and_more = @{ZipperT_arg 4}
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) GCSD.K.M.t
    where type (@{ParaT_args} 't, 's, 'i, 'o) L.lens = (@{ParaT_args} 't, 's, 'i, 'o) GCSD.L.lens
  ) : ZIPPY_WITH_GOALS_BASE =
struct

type gclusters = gclusters
type gcluster = gcluster
type focus = focus

structure GCSD = GCSD
type @{AllT_args} gcsd_more = @{AllT_args} gcsd_more
structure GCD = GCD
type @{AllT_args} gcd_more = @{AllT_args} gcd_more
structure FD = FD
type @{AllT_args} action_fd_more = @{AllT_args} action_fd_more
type @{AllT_args} actiona_fd_more = @{AllT_args} actiona_fd_more

open Z

structure Z = Instantiate_Zippy_With_PResults(
  \<^imap>\<open>\<open>{i}\<close> =>
  \<open>type @{AllT_args} inst{i} = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
  type @{AllT_args} inst1 = (gclusters, @{AllT_args} gcsd_more) GCSD.gclusters_data
  type @{AllT_args} inst2 = (gcluster, @{AllT_args} gcd_more) GCD.gcluster_data
  type @{AllT_args} inst4 = (focus, @{AllT_args} action_fd_more) FD.focus_data
  type @{AllT_args} inst5 = (focus, @{AllT_args} actiona_fd_more) FD.focus_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_Goals_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_GOALS_BASE
  ) :
    ZIPPY_WITH_GOALS_BASE
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
structure Z = Instantiate_Zippy_With_PResults(open Base; structure Z = Z)
open Z
end
