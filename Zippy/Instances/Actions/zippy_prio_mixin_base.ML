(*  Title:      Zippy/zippy_prio_mixin_base.ML
    Author:     Kevin Kappelmann

Priorities
*)
signature ZIPPY_PRIO_MIXIN_BASE =
sig
  type prio

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = prio
end

functor Zippy_Prio_Mixin_Base(
    type prio
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = @{ZipperT_arg 4}
  ) :
  sig
    structure DataM : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
    where type @{AllT_args} data = prio
    where type @{AllT_args} more = @{AllT_args} L.data

    include ZIPPY_PRIO_MIXIN_BASE
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT (ML_Gen.AllT_args () ^ " DataM.data_more") 5\<close>) L.container
    structure DataM_More : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{AllT_args} DataM.more
  end
  =
struct

type prio = prio

type @{AllT_args} container = (@{ParaT_args}
  @{ZipperT_args stop = 3},
  (prio, @{ZipperT_arg 4}) Data_MoreT.data_more) L.container

structure DataM = \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
  type @{AllT_args} data = prio
  type @{AllT_args} more = @{AllT_args} L.data)

structure Base =
struct
  type @{AllT_args} container = @{AllT_args} container
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
functor Instantiate_Zippy_Prio_Mixin_Base_{j}(
    type @{AllT_args} inst
    structure Prio : ZIPPY_PRIO_MIXIN_BASE
  ) :
    ZIPPY_PRIO_MIXIN_BASE
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Prio.L.container
  =  Prio\<close>\<close>
