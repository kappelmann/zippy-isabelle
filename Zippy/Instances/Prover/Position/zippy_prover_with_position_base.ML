(*  Title:      HOCLP/zippy_prover_with_position_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_WITH_POSITION_BASE =
sig
  structure ZPOS : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_POSITION_ZIPPER"\<close>
  structure ZDEPTH : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close>
  sharing type ZDEPTH.M.t = ZPOS.M.t
  sharing type ZDEPTH.L.lens = ZPOS.L.lens

  include ZIPPY_PROVER
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) ZPOS.M.t
  where type (@{ParaT_args} 't, 's, 'i, 'o) L.lens = (@{ParaT_args} 't, 's, 'i, 'o) ZPOS.L.lens

  (*lenses for position zippers*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val zpos_content{i} : unit ->
    (@{ParaT_args} @{AllT_args} Z{i}.ZO.content, @{AllT_args} ZPOS.N{i}.content) L.slens
  val zdepth_content{i} : unit ->
    (@{ParaT_args} @{AllT_args} Z{i}.ZO.content, @{AllT_args} ZDEPTH.Z{i}.ZO.content) L.slens\<close>\<close>
end

functor Zippy_Prover_With_Position_Base(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl = "(" ")"} exn = unit
    type prio
    type rd_more
  ) :
    ZIPPY_PROVER_WITH_POSITION_BASE
    where type @{AllT_args} gcsd_more = @{ZipperT_arg 0}
    where type @{AllT_args} gcd_more = @{ZipperT_arg 1}
    where type @{AllT_args} cd_more = @{ZipperT_arg 2}
    where type @{AllT_args} action_fd_more = @{ZipperT_arg 3}
    where type @{AllT_args} rdd_more = @{ZipperT_arg 4}
    where type prio = prio
    where type rd_more = rd_more
  =
struct

structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(M)
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception"\<close>(M))

structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens"\<close>(structure A = A
  structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens_Base"\<close>(AA.AA))
structure ZCOREAZ1 = \<^eval>\<open>sfx_T_nargs "Single_Content_Zipper"\<close>(
  structure AE = AE
  structure L = L
  type @{AllT_args} container = @{ZipperT_arg 0}
  type @{AllT_args} content = @{AllT_args} container
  val zip = M.pure
  val unzip = M.pure)
structure LZ = \<^eval>\<open>sfx_T_nargs "List_Zipper"\<close>(
  structure A = A
  structure L = L
  structure LI = \<^eval>\<open>sfx_ParaT_nargs "GList"\<close>(M)
  type @{AllT_args} content = @{ZipperT_arg 0}
  fun mk_exn_horizontal x = x |> A.K ())
structure ZCOREAZ2 = LZ
structure ZCOREAZ3 = LZ
structure ZCOREAZ4 = LZ
structure ZCOREAZ5 = LZ

structure ZCORE = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
  structure A = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} ncontent{i} = @{ZipperT_arg \<open>{i} - 1\<close>}
    structure Z{i} = ZCOREAZ{i}\<close>\<close>)
  structure ZD = \<^eval>\<open>sfx_ParaT_nargs "Zipper_Data"\<close>)
structure ZPOS = \<^eval>\<open>pfx_sfx_nargs "Alternating_Position_Zipper"\<close>(
  \<^eval>\<open>sfx_T_nargs "Position_Zipper"\<close>(
    structure A = AA
    structure L = L
    structure LI = LZ.LI))
structure ZDEPTH = \<^eval>\<open>pfx_sfx_nargs "Alternating_Depth_Zipper"\<close>(
  structure M = ZCORE
  structure L = L)
structure Z = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure AZ1 = ZCORE; structure AZ2 = ZPOS)
structure Z = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure AZ1 = Z; structure AZ2 = ZDEPTH)

structure CO = \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util_Apply"\<close>(
  structure CO = \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util"\<close>(
    structure AE = AE
    structure CO = \<^eval>\<open>sfx_ParaT_nargs "Coroutine"\<close>(A))
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(M))

structure ZP = Zippy_Prover(Zippy_Prover_Base(
  structure ZCOREAZ1 =
    struct open ZCOREAZ1 ZCORE.A.Z1; type @{AllT_args} container = @{AllT_args} ZCORE.N1.node end
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZCOREAZ{i} =
    struct open ZCOREAZ{i} ZCORE.A.Z{i}; type @{AllT_args} content = @{AllT_args} ZCORE.N{i}.node end\<close>
  where start = 2\<close>
  structure ZCORE = ZCORE
  structure Z = Z
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  fun zcore_content{i} _ = L.lens_fst (L.lens_fst (L.id ()))\<close>\<close>
  structure CO = CO
  type prio = prio
  type rd_more = rd_more))
open ZP

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun zpos_content{i} _ = L.lens_snd (L.lens_fst (L.id ())) \> ZPOS.N{i}.content\<close>\<close>
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun zdepth_content{i} _ = L.lens_snd (L.id ())\<close>\<close>

end

functor Instantiate_Zippy_Prover_With_Position_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_PROVER_WITH_POSITION_BASE
  ) :
    ZIPPY_PROVER_WITH_POSITION_BASE
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
structure Z = Instantiate_Zippy_Prover(open Base; structure Z = Z)
open Z
end

