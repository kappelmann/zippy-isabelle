(*  Title:      HOCLP/replace_zipper_content.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Content"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    type @{AllT_args} ncontent
    val ncontent : (@{ParaT_args} @{AllT_args} Z.ZO.content, @{AllT_args} ncontent) Z.cat
    val dest_ncontent : (@{ParaT_args} @{AllT_args} ncontent, @{AllT_args} Z.ZO.content) Z.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZM.container = @{AllT_args} Z.ZM.container
    where type @{AllT_args} ZO.content = @{AllT_args} ncontent
    where type @{AllT_args} ZO.zcontext = @{AllT_args} Z.ZO.zcontext
    where type @{AllT_args} zipper = @{AllT_args} Z.zipper
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  =
\<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZM = Z.ZM
  structure ZO = \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Optics_Content"\<close>(
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z.M)
    structure Z = Z.ZO
    type @{AllT_args} ncontent = @{AllT_args} ncontent
    val ncontent = ncontent
    val dest_ncontent = dest_ncontent
  )
)
