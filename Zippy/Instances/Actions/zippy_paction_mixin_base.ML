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

  structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = paction
  sharing type L.K.M.t = M.t

  type prio
  type @{AllT_args} action = prio -> (@{ParaT_args} @{AllT_args} zipper) hom_move

  val paction : (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) cat ->
    @{AllT_args} paction
  val run_paction : @{AllT_args} paction ->
    (@{ParaT_args} @{AllT_args} zipper, prio * @{AllT_args} action) cat
end

functor Zippy_PAction_Mixin_Base(
    structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} data = @{ZipperT_arg 3}
    type prio
  ) :
  sig
    structure DATAM : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
    where type @{AllT_args} more = @{ZipperT_arg 3}

    include ZIPPY_PACTION_MIXIN_BASE
    where type @{AllT_args} paction = @{AllT_args} DATAM.data
    where type @{AllT_args} L.container = (@{ParaT_args}
      @{ZipperT_args stop = 2},
      @{AllT_args} DATAM.data_more,
      @{ZipperT_args start = 4}) L.container
    structure MORE : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{ZipperT_arg 3}
  end
  =
struct

type prio = prio

structure MB = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(L.K.M)
open MB

datatype @{AllT_args} paction = PAction of (@{ParaT_args} @{AllT_args} zipper,
  prio * (prio -> (@{ParaT_args} @{AllT_args} zipper) hom_move)) cat
withtype
@{AllT_args} zipper = (@{ParaT_args}
  @{ZipperT_args stop = 2},
  (@{AllT_args} paction, @{ZipperT_arg 3}) Data_MoreT.data_more,
  @{ZipperT_args start = 4}) L.container

structure DATAM = \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
  structure L = L
  type @{AllT_args} data = @{AllT_args} paction
  type @{AllT_args} more = @{AllT_args} L.data)

type @{AllT_args} action = prio -> (@{ParaT_args} @{AllT_args} zipper) hom_move

fun paction paction = PAction paction
fun run_paction (PAction paction) = paction

structure Base =
struct
  structure L = L
  type @{AllT_args} container = @{AllT_args} zipper
  fun mk_lens l = L.comp l (L.lens ())
end
structure L = \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
  open Base
  type @{AllT_args} data = @{AllT_args} DATAM.data
  fun lens _ = mk_lens (DATAM.DATA.lens ()))
structure MORE = \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
  open Base
  type @{AllT_args} data = @{AllT_args} DATAM.more
  fun lens _ = mk_lens (DATAM.MORE.lens ()))

end
