(*  Title:      Zippy/modify_zipper_data_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Modify_Zipper_Data_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    type @{AllT_args} nzipper
    val nzipper : (@{ParaT_args} @{AllT_args} Z.zipper, @{AllT_args} nzipper) Z.L.C.cat
    val dest_nzipper : (@{ParaT_args} @{AllT_args} nzipper, @{AllT_args} Z.zipper) Z.L.C.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    where type @{AllT_args} content = @{AllT_args} Z.content
    where type @{AllT_args} zcontext = @{AllT_args} Z.zcontext
    where type @{AllT_args} zipper = @{AllT_args} nzipper
  =
struct

open Z

type @{AllT_args} zipper = @{AllT_args} nzipper
fun zipper x = x |> (L.C.comp nzipper Z.zipper)

structure Base =
struct
  type @{AllT_args} ncontainer = @{AllT_args} nzipper
  val ncontainer = nzipper
  val dest_ncontainer = dest_nzipper
end
structure CO = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Container"\<close>(
  open Base; structure L = CO)
structure ZCTXT = \<^eval>\<open>sfx_T_nargs "Modify_Structured_Lens_Container"\<close>(
  open Base; structure L = ZCTXT)

end
