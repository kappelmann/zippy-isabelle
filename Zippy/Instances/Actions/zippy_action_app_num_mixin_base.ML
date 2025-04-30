(*  Title:      Zippy/zippy_action_app_num_mixin_base.ML
    Author:     Kevin Kappelmann

Action application numbers.
*)
signature ZIPPY_ACTION_APP_NUM_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} zipper
  structure ACTIONAN : ZIPPY_ACTION_APP_NUM

  structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = ACTIONAN.action_app_num
  sharing type L.container = zipper
  sharing type L.K.M.t = M.t
end

(* functor Zippy_With_PAction_Mixin_Base(
    type copy_update_data
    type prio
    structure CD : KLEISLI_ZIPPY_COPY_DATA
    type @{AllT_args} cd_more
    structure PAD : ZIPPY_PACTION_DATA
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) CD.L.C.cat
    sharing type PAD.L.lens = CD.L.lens
    type @{AllT_args} pad_more
    structure PD : ZIPPY_PRIO_DATA
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) CD.L.C.cat
    sharing type PD.L.lens = CD.L.lens
    type @{AllT_args} pd_more

    structure ZCORE : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
    where type @{AllT_args} N3.content = @{ZipperT_arg 2}
    where type @{AllT_args} N4.content = @{ZipperT_arg 3}
    where type @{AllT_args} N5.content = @{ZipperT_arg 4}
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) CD.K.M.t
    sharing type ZCORE.L.lens = CD.L.lens

    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) ZCORE.M.t
    sharing type Z.L.lens = ZCORE.L.lens

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val zcore_content{i} : unit ->
      (@{ParaT_args} @{AllT_args} Z.Z{i}.ZD.content, @{AllT_args} ZCORE.Z{i}.ZD.content) Z.L.slens\<close>\<close>
  ) : ZIPPY_WITH_PACTION_MIXIN_BASE =
struct

type copy_update_data = copy_update_data
type prio = prio
structure CD = CD
type @{AllT_args} cd_more = @{AllT_args} cd_more
structure PAD = PAD
type @{AllT_args} pad_more = @{AllT_args} pad_more
structure PD = PD
type @{AllT_args} pd_more = @{AllT_args} pd_more

structure ZCORE = ZCORE
open Z

\<^imap>\<open>\<open>{i}\<close> => \<open>
val zcore_content{i} = zcore_content{i}\<close>\<close>

(* paction *)
datatype (@{AllT_args encl = "" ","} 'padm) paction = PAction of
  (@{ParaT_args} (@{AllT_args encl = "" ","} 'padm) zipper4,
    prio * (prio -> (@{ParaT_args} (@{AllT_args encl = "" ","} 'padm) zipper4) hom_move)) cat
withtype \<^imap>\<open>\<open>{i}\<close> => \<open>
(@{AllT_args encl = "" ","} 'padm) zipper{i} = (@{ParaT_args} @{ZipperT_args stop = 2},
  ((@{AllT_args encl = "" ","} 'padm) paction, 'padm) PAD.paction_data, @{ZipperT_arg 4}) Z{i}.zipper\<close>
where sep = "and"\<close>

fun mk_paction paction = PAction paction
fun dest_paction (PAction paction) = paction

(* copy *)
datatype (@{AllT_args encl = "" ","} 'padm, 'cdm) copy = Copy of copy_update_data ->
  (@{AllT_args encl = "" ","} 'padm, 'cdm) zipper3 -> (@{ParaT_args}
    (@{AllT_args encl = "" ","} 'padm, 'cdm) zipper1) hom_move
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
(@{AllT_args encl = "" ","} 'padm, 'cdm) zipper{i} = (@{ParaT_args} @{ZipperT_args stop = 1},
  ((@{AllT_args encl = "" ","} 'padm, 'cdm) copy, 'cdm) CD.copy_data,
  @{ZipperT_args start = 3}, 'padm) zipper{i}\<close>
where sep = "and"\<close>
and (@{AllT_args encl = "" ","} 'padm, 'cdm) paction = (@{ParaT_args} @{ZipperT_args stop = 1},
  ((@{AllT_args encl = "" ","} 'padm, 'cdm) copy, 'cdm) CD.copy_data,
  @{ZipperT_args start = 3}, 'padm) paction

fun mk_copy copy = Copy copy
fun dest_copy (Copy copy) = copy

(* priority *)
(* type \<^imap>\<open>\<open>{i}\<close> => \<open>
(@{AllT_args encl = "" ","} 'padm, 'cdm, 'pdm) zipper{i} =
  (@{ParaT_args} @{ZipperT_args stop = 3}, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) zipper{i}\<close>
where sep = "and"\<close>
and (@{AllT_args encl = "" ","} 'padm, 'cdm, 'pdm) paction =
  (@{ParaT_args} @{ZipperT_args stop = 3}, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) paction
and (@{AllT_args encl = "" ","} 'padm, 'cdm, 'pdm) copy =
  (@{ParaT_args} @{ZipperT_args stop = 3}, (prio, 'pdm) PD.prio_data, 'padm, 'cdm) copy *)

type \<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} zipper{i} = (@{AllT_args encl = "" ","}
  @{AllT_args} pad_more, @{AllT_args} cd_more) zipper{i}\<close>
where sep = "and"\<close>
and @{AllT_args} paction = (@{AllT_args encl = "" ","}
  @{AllT_args} pad_more, @{AllT_args} cd_more) paction
and @{AllT_args} copy = (@{AllT_args encl = "" ","}
  @{AllT_args} pad_more, @{AllT_args} cd_more) copy

type @{AllT_args} action = prio -> (@{ParaT_args} @{AllT_args} zipper4) hom_move

structure Base =
struct type @{AllT_args} inst = (@{AllT_args} copy, @{AllT_args} cd_more) CD.copy_data end
structure ZCORE = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper_Nodes" 3]\<close>(
  open Base; structure Z = ZCORE)
structure Z = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper" 3]\<close>(
  open Base; structure Z = Z)

structure Base =
struct type @{AllT_args} inst = (@{AllT_args} paction, @{AllT_args} pad_more) PAD.paction_data end
structure ZCORE = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper_Nodes" 4]\<close>(
  open Base; structure Z = ZCORE)
structure Z = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper" 4]\<close>(
  open Base; structure Z = Z)

(* structure Base =
struct type @{AllT_args} inst = (prio, @{AllT_args} pd_more) PD.prio_data end
structure ZCORE = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper_Nodes" 5]\<close>(
  open Base; structure Z = ZCORE)
structure Z = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper" 5]\<close>(
  open Base; structure Z = Z) *)

open Z

end *)

(* functor Instantiate_Zippy_With_PAction_Mixin_Base(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : ZIPPY_WITH_PACTION_MIXIN_BASE
  ) :
    ZIPPY_WITH_PACTION_MIXIN_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.A.Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZM.container
    where type @{AllT_args} ZCORE.A.Z{i}.ZD.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZD.content
    where type @{AllT_args} ZCORE.A.Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.ZCORE.A.Z{i}.ZD.zcontext
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
    where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZD.content
    where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.Z{i}.zipper\<close>\<close>
    where type @{AllT_args} cd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.cd_more
    where type @{AllT_args} pad_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.pad_more
    where type @{AllT_args} pd_more = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.pd_more
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.paction
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.copy =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure ZCORE = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_nargs "Alternating_Zipper_Nodes"]\<close>(
  open Base; structure Z = ZCORE)
structure Z = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  open Base; structure Z = Z)
open Z
end *)
