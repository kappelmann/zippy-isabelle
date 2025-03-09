(*  Title:      HOCLP/zippy_prover_with_position_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_WITH_POSITION_BASE =
sig
  structure ZPOS : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_POSITION_ZIPPERS"\<close>
  structure ZDEPTH : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_DEPTH_ZIPPERS"\<close>
  sharing type ZDEPTH.M.t = ZPOS.M.t
  sharing type ZDEPTH.L.lens = ZPOS.L.lens

  include ZIPPY_PROVER
  where type ('p1, 'a) M.t = ('p1, 'a) ZPOS.M.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) ZPOS.L.lens

  (*lenses for position zippers*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val zpos_content{i} : unit ->
    (@{ParaT_args}, @{T_args} Z{i}.ZO.content, @{T_args} ZPOS.N{i}.content) L.slens
  val zdepth_content{i} : unit ->
    (@{ParaT_args}, @{T_args} Z{i}.ZO.content, @{T_args} ZDEPTH.Z{i}.ZO.content) L.slens\<close>\<close>
end

functor Zippy_Prover_With_Position_Base(
    structure M : MONAD_EXCEPTION_BASE
    where type 'p1 exn = unit
    type prio
    type rd_more
  ) :
    ZIPPY_PROVER_WITH_POSITION_BASE
    where type @{T_args} gcsd_more = @{PolyT_arg 0}
    where type @{T_args} gcd_more = @{PolyT_arg 1}
    where type @{T_args} cd_more = @{PolyT_arg 2}
    where type @{T_args} action_fd_more = @{PolyT_arg 3}
    where type @{T_args} rdd_more = @{PolyT_arg 4}
    where type prio = prio
    where type rd_more = rd_more
  =
struct

structure A = Kleisli_Arrow(M)
structure AA = Kleisli_Arrow_Arrow_Apply(M)
structure AE = Kleisli_Arrow_Exception_Rec(Kleisli_Arrow_Exception(M))

structure L = Lens(structure A = A; structure L = Lens_Base(AA.AA))
structure ZCOREAZ1 = \<^eval>\<open>T_Args.suffix_Poly_nargs "Single_Content_Zipper"\<close>(
  structure AE = AE
  structure L = L
  type @{T_args} container = @{PolyT_arg 0}
  type @{T_args} content = @{T_args} container
  val zip = M.pure
  val unzip = M.pure)
structure LZ = \<^eval>\<open>T_Args.suffix_Poly_nargs "List_Zipper"\<close>(
  structure A = A
  structure L = L
  structure LI = GList(M)
  type @{T_args} content = @{PolyT_arg 0}
  fun mk_exn_horizontal x = x |> A.K ())
structure ZCOREAZ2 = LZ
structure ZCOREAZ3 = LZ
structure ZCOREAZ4 = LZ
structure ZCOREAZ5 = LZ

structure ZCORE = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes"\<close>(
  structure A = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{T_args} ncontent{i} = @{PolyT_arg \<open>{i} - 1\<close>}
    structure Z{i} = ZCOREAZ{i}\<close>\<close>)
  structure ZD = Zipper_Data)
structure ZPOS = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Position_Zippers"\<close>(
  \<^eval>\<open>T_Args.suffix_Poly_nargs "Position_Zipper"\<close>(
    structure A = AA
    structure L = L
    structure LI = LZ.LI))
structure ZDEPTH = \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Depth_Zippers"\<close>(
  structure M = ZCORE
  structure L = L)
structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Alternating_Zippers"\<close>(
  structure AZ1 = ZCORE; structure AZ2 = ZPOS)
structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Pair_Alternating_Zippers"\<close>(
  structure AZ1 = Z; structure AZ2 = ZDEPTH)

structure CO = Coroutine_Util_Apply(
  structure CO = Coroutine_Util(structure AE = AE; structure CO = Coroutine(A))
  structure A = Kleisli_Arrow_Arrow_Apply(M))

structure ZP = Zippy_Prover(Zippy_Prover_Base(
  structure ZCOREAZ1 =
    struct open ZCOREAZ1 ZCORE.A.Z1; type @{T_args} container = @{T_args} ZCORE.N1.node end
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZCOREAZ{i} =
    struct open ZCOREAZ{i} ZCORE.A.Z{i}; type @{T_args} content = @{T_args} ZCORE.N{i}.node end\<close>
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
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_PROVER_WITH_POSITION_BASE
  ) :
    ZIPPY_PROVER_WITH_POSITION_BASE
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
structure Z = Instantiate_Zippy_Prover(open Base; structure Z = Z)
open Z
end

