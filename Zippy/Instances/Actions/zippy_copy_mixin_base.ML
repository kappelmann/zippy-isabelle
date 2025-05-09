(*  Title:      Zippy/zippy_copy_mixin_base.ML
    Author:     Kevin Kappelmann

Copy mechanism.
*)
signature ZIPPY_COPY_MIXIN_BASE =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} copy
  type @{AllT_args} zipper_from
  type @{AllT_args} zipper_to

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type L.container = zipper_from
  sharing type L.data = copy

  type copy_update_data

  val copy : (copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move) -> @{AllT_args} copy
  val run_copy : @{AllT_args} copy -> copy_update_data ->
    @{AllT_args} zipper_from -> (@{ParaT_args} @{AllT_args} zipper_to) hom_move
end

functor Zippy_Copy_Mixin_Base(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = @{ZipperT_arg 2}
    type @{AllT_args} zipper_to
    type copy_update_data
  ) :
  sig
    structure DataM : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
    where type @{AllT_args} more = @{AllT_args} L.data

    include ZIPPY_COPY_MIXIN_BASE
    where type @{AllT_args} copy = @{AllT_args} DataM.data
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT (ML_Gen.AllT_args () ^ " DataM.data_more") 3\<close>) L.container
    structure DataM_More : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{AllT_args} DataM.more
  end
  =
struct

open M
type copy_update_data = copy_update_data

datatype @{AllT_args} copy = Copy of copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move
withtype
@{AllT_args} zipper_from = (@{ParaT_args}
  @{ZipperT_args stop = 1},
  (@{AllT_args} copy, @{ZipperT_arg 2}) Data_MoreT.data_more,
  @{ZipperT_args start = 3}) L.container
and @{AllT_args} zipper_to = (@{ParaT_args}
  @{ZipperT_args stop = 1},
  (@{AllT_args} copy, @{ZipperT_arg 2}) Data_MoreT.data_more,
  @{ZipperT_args start = 3}) zipper_to

structure DataM = \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
  type @{AllT_args} data = @{AllT_args} copy
  type @{AllT_args} more = @{AllT_args} L.data)

fun copy copy = Copy copy
fun run_copy (Copy copy) = copy

structure Base =
struct
  type @{AllT_args} container = @{AllT_args} zipper_from
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
functor Instantiate_Zippy_Copy_Mixin_Base_{j}(
    type @{AllT_args} inst
    structure Copy : ZIPPY_COPY_MIXIN_BASE
  ) :
    ZIPPY_COPY_MIXIN_BASE
    where type @{AllT_args} copy = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Copy.copy
    where type @{AllT_args} zipper_from = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Copy.zipper_from
    where type @{AllT_args} zipper_to = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Copy.zipper_to
  =  Copy\<close>\<close>
