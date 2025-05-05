(*  Title:      Zippy/data_more.ML
    Author:     Kevin Kappelmann
*)
structure Data_MoreT =
struct
  type ('d, 'm) data_more = {data : 'd, more : 'm}
end

signature \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
  type @{AllT_args} data
  type @{AllT_args} more
  type @{AllT_args} data_more = (@{AllT_args} data, @{AllT_args} more) Data_MoreT.data_more

  val data_more : @{AllT_args} more -> @{AllT_args} data -> @{AllT_args} data_more

  structure DATA : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} data_more
  where type @{AllT_args} data = @{AllT_args} data
  sharing type DATA.lens = L.lens
  sharing type DATA.K.M.t = L.K.M.t

  structure MORE : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} data_more
  where type @{AllT_args} data = @{AllT_args} more
  sharing type MORE.lens = L.lens
  sharing type MORE.K.M.t = L.K.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Data_More"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
    type @{AllT_args} data
    type @{AllT_args} more
  ) : \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
  =
struct

structure L = L

type @{AllT_args} data = @{AllT_args} data
type @{AllT_args} more = @{AllT_args} more
type @{AllT_args} data_more = (@{AllT_args} data, @{AllT_args} more) Data_MoreT.data_more

local open L.K.M
in

fun data_more more data = {data = data, more = more}

structure Base = struct open L; type @{AllT_args} container = @{AllT_args} data_more end
structure DATA =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} data
  fun getter {data,...} = pure data
  fun modifier (f, {data, more}) = bind (f data)
    (fn data => pure (data_more more data))
  fun lens _ = L.mk_lens getter modifier
end

structure MORE =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} more
  fun getter {more,...} = pure more
  fun modifier (f, {data, more}) = bind (f more)
    (fn more => pure (data_more more data))
  fun lens _ = L.mk_lens getter modifier
end
end

end
