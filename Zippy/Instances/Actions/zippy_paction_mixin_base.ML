(*  Title:      Zippy/zippy_paction_mixin_base.ML
    Author:     Kevin Kappelmann

Prioritised actions.
*)
signature ZIPPY_PACTION_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  (*prioritised actions*)
  type @{AllT_args} paction
  type @{AllT_args} zipper

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = paction

  type prio
  type @{AllT_args} action = prio -> (@{ParaT_args} @{AllT_args} zipper) hom_move

  val paction : (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) cat ->
    @{AllT_args} paction
  val run_paction : @{AllT_args} paction ->
    (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) cat
end

functor Zippy_PAction_Mixin_Base(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = @{ZipperT_arg 3}
    type prio
  ) :
  sig
    structure DataM : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
    where type @{AllT_args} more = @{AllT_args} L.data

    include ZIPPY_PACTION_MIXIN_BASE
    where type @{AllT_args} paction = @{AllT_args} DataM.data
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT (ML_Gen.AllT_args () ^ " DataM.data_more") 4\<close>) L.container
    structure DataM_More : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{AllT_args} DataM.more
  end
  =
struct

open M
type prio = prio

datatype @{AllT_args} paction = PAction of (@{ParaT_args} @{AllT_args} zipper,
  prio * (prio -> (@{ParaT_args} @{AllT_args} zipper) hom_move)) cat
withtype
@{AllT_args} zipper = (@{ParaT_args}
  @{ZipperT_args stop = 2},
  (@{AllT_args} paction, @{ZipperT_arg 3}) Data_MoreT.data_more,
  @{ZipperT_args start = 4}) L.container

structure DataM = \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
  type @{AllT_args} data = @{AllT_args} paction
  type @{AllT_args} more = @{AllT_args} L.data)

type @{AllT_args} action = prio -> (@{ParaT_args} @{AllT_args} zipper) hom_move

fun paction paction = PAction paction
fun run_paction (PAction paction) = paction

structure Base =
struct
  type @{AllT_args} container = @{AllT_args} zipper
  fun mk_lens l = L.comp l (L.lens ())
end
structure L = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  open Base
  type @{AllT_args} data = @{AllT_args} DataM.data
  fun lens _ = mk_lens (DataM.Data.lens ()))
structure DataM_More = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  open Base
  type @{AllT_args} data = @{AllT_args} DataM.more
  fun lens _ = mk_lens (DataM.More.lens ()))

end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Instantiate_Zippy_PAction_Mixin_Base_{j}(
    type @{AllT_args} inst
    structure PAction : ZIPPY_PACTION_MIXIN_BASE
  ) :
    ZIPPY_PACTION_MIXIN_BASE
    where type @{AllT_args} paction = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) PAction.paction
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) PAction.zipper
  =  PAction\<close>\<close>
