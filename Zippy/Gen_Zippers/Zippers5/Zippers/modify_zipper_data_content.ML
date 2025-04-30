(*  Title:      Zippy/modify_zipper_data_content.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Data_Content"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    type @{AllT_args} ncontent
    val ncontent : (@{ParaT_args} @{AllT_args} Z.content, @{AllT_args} ncontent) Z.L.C.cat
    val dest_ncontent : (@{ParaT_args} @{AllT_args} ncontent, @{AllT_args} Z.content) Z.L.C.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    where type @{AllT_args} content = @{AllT_args} ncontent
    where type @{AllT_args} zcontext = @{AllT_args} Z.zcontext
    where type @{AllT_args} zipper = @{AllT_args} Z.zipper
  =
struct

open Z

type @{AllT_args} content = @{AllT_args} ncontent
local structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(L.K.M) open A
in
fun zipper x = x |> (comp Z.zipper (first dest_ncontent))
end

structure CO = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Data"\<close>(
  type @{AllT_args} ndata = @{AllT_args} ncontent
  val ndata = ncontent
  val dest_ndata = dest_ncontent
  structure L = CO)

end
