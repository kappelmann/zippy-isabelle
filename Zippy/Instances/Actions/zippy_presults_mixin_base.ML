(*  Title:      Zippy/zippy_presults_mixin_base.ML
    Author:     Kevin Kappelmann

Prioritised results.
*)
signature ZIPPY_PRESULTS_MIXIN_BASE =
sig
  type @{AllT_args} presults
  type @{AllT_args} zipper

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper
  sharing type L.data = presults

  type prio
  type result
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>

  val presults : (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.acoroutine ->
    @{AllT_args} presults
  val dest_presults : @{AllT_args} presults ->
    (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.acoroutine
end

functor Zippy_PResults_Mixin_Base(
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = @{ZipperT_arg 3}
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    type prio
    type result
  ) :
  sig
    structure DataM : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
    where type @{AllT_args} more = @{AllT_args} L.data

    include ZIPPY_PRESULTS_MIXIN_BASE
    where type @{AllT_args} presults = @{AllT_args} DataM.data
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT (ML_Gen.AllT_args () ^ " DataM.data_more") 4\<close>) L.container
    structure DataM_More : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{AllT_args} DataM.more
  end
  =
struct

structure Co = Co
type prio = prio
type result = result

datatype @{AllT_args} presults = PResults of
  (@{ParaT_args} @{AllT_args} zipper, prio, result) Co.acoroutine
withtype
@{AllT_args} zipper = (@{ParaT_args}
  @{ZipperT_args stop = 2},
  (@{AllT_args} presults, @{ZipperT_arg 3}) Data_MoreT.data_more,
  @{ZipperT_args start = 4}) L.container

structure DataM = \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
  type @{AllT_args} data = @{AllT_args} presults
  type @{AllT_args} more = @{AllT_args} L.data)

fun presults presults = PResults presults
fun dest_presults (PResults presults) = presults

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
functor Instantiate_Zippy_Presults_Mixin_Base_{j}(
    type @{AllT_args} inst
    structure Presults : ZIPPY_PRESULTS_MIXIN_BASE
  ) :
    ZIPPY_PRESULTS_MIXIN_BASE
    where type @{AllT_args} presults = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Presults.presults
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Presults.zipper
  =  Presults\<close>\<close>
