(*  Title:      HOCLP/replace_zipper_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Zipper"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    type @{AllT_args} nzipper
    val nzipper : (@{ParaT_args} @{AllT_args} Z.zipper, @{AllT_args} nzipper) Z.cat
    val dest_nzipper : (@{ParaT_args} @{AllT_args} nzipper, @{AllT_args} Z.zipper) Z.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZM.container = @{AllT_args} Z.ZM.container
    where type @{AllT_args} ZO.content = @{AllT_args} Z.ZO.content
    where type @{AllT_args} ZO.zcontext = @{AllT_args} Z.ZO.zcontext
    where type @{AllT_args} zipper = @{AllT_args} nzipper
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  =
\<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure Base =
  struct
    type @{AllT_args} nzipper = @{AllT_args} nzipper
    val nzipper = nzipper
    val dest_nzipper = dest_nzipper
  end
  structure ZM = \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Moves_Zipper"\<close>(
    open Base; structure Z = Z.ZM)
  structure ZO = \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Optics_Zipper"\<close>(
    open Base; structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z.M); structure Z = Z.ZO)
)
