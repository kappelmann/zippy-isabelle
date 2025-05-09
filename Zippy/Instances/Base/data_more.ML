(*  Title:      Zippy/data_more.ML
    Author:     Kevin Kappelmann
*)
structure Data_MoreT =
struct
  type ('d, 'm) data_more = {data : 'd, more : 'm}
end

signature \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close> =
sig
  type @{AllT_args} data
  type @{AllT_args} more
  type @{AllT_args} data_more = (@{AllT_args} data, @{AllT_args} more) Data_MoreT.data_more

  val data_more : @{AllT_args} more -> @{AllT_args} data -> @{AllT_args} data_more

  structure Data : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} data_more
  where type @{AllT_args} data = @{AllT_args} data

  structure More : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} data_more
  where type @{AllT_args} data = @{AllT_args} more
end

functor \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
    type @{AllT_args} data
    type @{AllT_args} more
  ) : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
  =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>

type @{AllT_args} data = @{AllT_args} data
type @{AllT_args} more = @{AllT_args} more
type @{AllT_args} data_more = (@{AllT_args} data, @{AllT_args} more) Data_MoreT.data_more

fun data_more more data = {data = data, more = more}

structure Base = struct open L; type @{AllT_args} container = @{AllT_args} data_more end
structure Data =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} data
  fun getter {data,...} = data
  fun modifier (f, {data, more}) = data_more more (f data)
  fun lens _ = L.mk_lens getter modifier
end

structure More =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} more
  fun getter {more,...} = more
  fun modifier (f, {data, more}) = data_more (f more) data
  fun lens _ = L.mk_lens getter modifier
end

end
