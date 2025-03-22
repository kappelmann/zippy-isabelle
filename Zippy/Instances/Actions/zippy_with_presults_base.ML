(*  Title:      Zippy/zippy_with_presults_base.ML
    Author:     Kevin Kappelmann

Zippy with prioritised action results.
*)
signature ZIPPY_WITH_PRESULTS_BASE =
sig
  type result
  (** action application number **)
  type actiona_num = int
  val init_actiona_num : int
  val inc_actiona_num : int -> int

  structure PRD : KLEISLI_ZIPPY_PRESULTS_DATA
  structure AND : ZIPPY_ACTIONA_NUM_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) PRD.L.C.cat
  sharing type AND.L.lens = PRD.L.lens
  type @{AllT_args} action_and_more
  type @{AllT_args} actiona_and_more

  type @{AllT_args} presults

  include ZIPPY_WITH_PACTION
  where type @{AllT_args} pad_more = (@{AllT_args} presults,
    (actiona_num, @{AllT_args} action_and_more) AND.actiona_num_data) PRD.presults_data
  where type @{AllT_args} pd_more =
    (actiona_num, @{AllT_args} actiona_and_more) AND.actiona_num_data
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) PRD.K.M.t
  where type (@{ParaT_args} 't, 's, 'i, 'o) L.lens = (@{ParaT_args} 't, 's, 'i, 'o) PRD.L.lens

  val mk_presults : (@{ParaT_args} @{AllT_args} Z4.zipper, prio, result) CO.acoroutine ->
    @{AllT_args} presults
  val dest_presults : @{AllT_args} presults ->
    (@{ParaT_args} @{AllT_args} Z4.zipper, prio, result) CO.acoroutine
end

functor Zippy_With_PResults_Base(
    type result
    structure PRD : KLEISLI_ZIPPY_PRESULTS_DATA
    structure AND : ZIPPY_ACTIONA_NUM_DATA
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) PRD.L.C.cat
    sharing type AND.L.lens = PRD.L.lens
    type @{AllT_args} action_and_more
    type @{AllT_args} actiona_and_more

    structure Z : ZIPPY_WITH_PACTION
    where type @{AllT_args} pad_more = @{ZipperT_arg 3}
    where type @{AllT_args} pd_more = @{ZipperT_arg 4}
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) PRD.K.M.t
    where type (@{ParaT_args} 't, 's, 'i, 'o) L.lens = (@{ParaT_args} 't, 's, 'i, 'o) PRD.L.lens
  ) : ZIPPY_WITH_PRESULTS_BASE =
struct

type result = result
(** action number **)
type actiona_num = int
val init_actiona_num = 0
val inc_actiona_num = General_Util.succ

structure PRD = PRD
structure AND = AND
type @{AllT_args} action_and_more = @{AllT_args} action_and_more
type @{AllT_args} actiona_and_more = @{AllT_args} actiona_and_more

open Z
datatype (@{AllT_args encl = "" ""}, 'prdm) presults = PResults of
  (@{ParaT_args} (@{AllT_args encl = "" ""}, 'prdm) zipper4, prio, result) CO.acoroutine
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
(@{AllT_args encl = "" ""}, 'prdm) zipper{i} = (@{ParaT_args} @{ZipperT_args stop = 2},
  ((@{AllT_args encl = "" ""}, 'prdm) presults, 'prdm) PRD.presults_data, @{ZipperT_arg 4}) Z{i}.zipper\<close>
where sep = "and"\<close>

fun mk_presults presults = PResults presults
fun dest_presults (PResults presults) = presults

type @{AllT_args} presults = (@{ParaT_args} @{ZipperT_args stop = 3},
  (actiona_num, @{AllT_args} actiona_and_more) AND.actiona_num_data,
  (actiona_num, @{AllT_args} action_and_more) AND.actiona_num_data) presults

structure Z = Instantiate_Zippy_With_PAction(
  \<^imap>\<open>\<open>{i}\<close> =>
  \<open>type @{AllT_args} inst{i} = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
  type @{AllT_args} inst4 = (@{AllT_args} presults,
    (actiona_num, @{AllT_args} action_and_more) AND.actiona_num_data) PRD.presults_data
  type @{AllT_args} inst5 = (actiona_num, @{AllT_args} actiona_and_more) AND.actiona_num_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_PResults_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_PRESULTS_BASE
  ) :
    ZIPPY_WITH_PRESULTS_BASE
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
    where type @{AllT_args} ZCORE.A.N{i}.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.N{i}.content\<close>
    where stop = 2\<close>
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
    where type @{AllT_args} cd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{AllT_args} action_and_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.action_and_more
    where type @{AllT_args} actiona_and_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.actiona_and_more
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{AllT_args} presults = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_With_PAction(open Base; structure Z = Z)
open Z
end
