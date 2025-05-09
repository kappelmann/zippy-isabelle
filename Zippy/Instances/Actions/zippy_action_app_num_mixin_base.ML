(*  Title:      Zippy/zippy_action_app_num_mixin_base.ML
    Author:     Kevin Kappelmann

Action application numbers.
*)
signature ZIPPY_ACTION_APP_NUM_MIXIN_BASE =
sig
  structure AAN : ZIPPY_ACTION_APP_NUM

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = AAN.action_app_num
end

functor Zippy_Action_App_Num_Mixin_Base(
    L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = @{ZipperT_arg 3}
  ) :
  sig
    structure DataM : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
    where type @{AllT_args} data = Zippy_Action_App_Num.action_app_num
    where type @{AllT_args} more = @{AllT_args} L.data

    include ZIPPY_ACTION_APP_NUM_MIXIN_BASE
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT (ML_Gen.AllT_args () ^ " DataM.data_more") 4\<close>) L.container
    structure DataM_More : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} L.container
    where type @{AllT_args} data = @{AllT_args} DataM.more
  end
  =
struct

structure AAN = Zippy_Action_App_Num

type @{AllT_args} container = (@{ParaT_args}
  @{ZipperT_args stop = 2},
  (AAN.action_app_num, @{ZipperT_arg 3}) Data_MoreT.data_more,
  @{ZipperT_args start = 4}) L.container

structure DataM = \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
  type @{AllT_args} data = AAN.action_app_num
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
functor Instantiate_Zippy_Action_App_Num_Mixin_Base_{j}(
    type @{AllT_args} inst
    structure ActionAN : ZIPPY_ACTION_APP_NUM_MIXIN_BASE
  ) :
    ZIPPY_ACTION_APP_NUM_MIXIN_BASE
    where type @{AllT_args} L.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) ActionAN.L.container
  =  ActionAN\<close>\<close>
