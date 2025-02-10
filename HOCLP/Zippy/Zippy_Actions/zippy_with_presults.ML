(*  Title:      HOCLP/zippy_with_presults.ML
    Author:     Kevin Kappelmann

Zippy with prioritised action results.
*)
signature ZIPPY_WITH_PRESULTS =
sig
  type result
  (** action number **)
  type action_num = int
  val init_action_num : int
  val next_action_num : int -> int

  structure PRD : KLEISLI_ZIPPY_PRESULTS_DATA
  structure AND : ZIPPY_ACTION_NUM_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) PRD.L.C.cat
  sharing type AND.L.lens = PRD.L.lens
  type @{T_args} action_and_more
  type @{T_args} aaction_and_more

  type @{T_args} presults

  include ZIPPY_WITH_PACTION
  where type @{T_args} pad_more = (@{T_args} presults,
    (action_num, @{T_args} action_and_more) AND.action_num_data) PRD.presults_data
  where type @{T_args} pd_more = (action_num,
    @{T_args} aaction_and_more) AND.action_num_data
  where type ('p1, 'a) M.t = ('p1, 'a) PRD.K.M.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) PRD.L.lens

  structure CO : COROUTINE
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) cat

  val mk_presults : ('p1, @{T_args} Z4.zipper, prio, result) CO.acoroutine -> @{T_args} presults
  val dest_presults : @{T_args} presults -> ('p1, @{T_args} Z4.zipper, prio, result) CO.acoroutine
end

functor Zippy_With_PResults(
    type result
    structure PRD : KLEISLI_ZIPPY_PRESULTS_DATA
    structure AND : ZIPPY_ACTION_NUM_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) PRD.L.C.cat
    sharing type AND.L.lens = PRD.L.lens
    type @{T_args} action_and_more
    type @{T_args} aaction_and_more

    structure Z : ZIPPY_WITH_PACTION
    where type @{T_args} pad_more = @{PolyT_arg 3}
    where type @{T_args} pd_more = @{PolyT_arg 4}
    where type ('p1, 'a) M.t = ('p1, 'a) PRD.K.M.t
    where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) PRD.L.lens

    structure CO : COROUTINE
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) Z.cat
  ) : ZIPPY_WITH_PRESULTS =
struct

type result = result
(** action number **)
type action_num = int
val init_action_num = 0
val next_action_num = General_Util.succ

structure PRD = PRD
structure AND = AND
type @{T_args} action_and_more = @{T_args} action_and_more
type @{T_args} aaction_and_more = @{T_args} aaction_and_more
structure CO = CO

open Z
datatype (@{T_args encl = "" ""}, 'prdm) presults = PResults of
  (@{ParaT_args}, (@{T_args encl = "" ""}, 'prdm) zipper4, prio, result) CO.acoroutine
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
(@{T_args encl = "" ""}, 'prdm) zipper{i} = (@{ParaT_args}, @{PolyT_args stop = 2},
  ((@{T_args encl = "" ""}, 'prdm) presults, 'prdm) PRD.presults_data, @{PolyT_arg 4}) Z{i}.zipper\<close>
where sep = "and"\<close>

fun mk_presults presults = PResults presults
fun dest_presults (PResults presults) = presults

type @{T_args} presults = (@{ParaT_args}, @{PolyT_args stop = 3},
  (action_num, @{T_args} aaction_and_more) AND.action_num_data,
  (action_num, @{T_args} action_and_more) AND.action_num_data) presults

structure Z = Instantiate_Zippy_With_PAction(
  \<^imap>\<open>\<open>{i}\<close> =>
  \<open>type @{T_args} inst{i} = @{PolyT_arg \<open>{i} - 1\<close>}\<close>\<close>
  type @{T_args} inst4 = (@{T_args} presults,
    (action_num, @{T_args} action_and_more) AND.action_num_data) PRD.presults_data
  type @{T_args} inst5 = (action_num, @{T_args} aaction_and_more) AND.action_num_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_PResults(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_PRESULTS
  ) :
    ZIPPY_WITH_PRESULTS
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
    where type @{T_args} A.N{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.N{i}.content\<close>
    where stop = 2\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} zcontext{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.zcontext{i}
    where type @{T_args} pzipper{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.pzipper{i}\<close>\<close>
    where type @{T_args} cd_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{T_args} action_and_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.action_and_more
    where type @{T_args} aaction_and_more = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.aaction_and_more
    where type @{T_args} paction = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{T_args} copy = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.copy
    where type @{T_args} presults = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.presults =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure Z = Instantiate_Zippy_With_PAction(open Base; structure Z = Z)
open Z
end
