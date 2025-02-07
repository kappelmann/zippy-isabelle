(*  Title:      HOCLP/replace_zipper_content.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Content"\<close>(
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    type @{T_args} ncontent
    val ncontent : (@{ParaT_args}, @{T_args} Z.ZO.content, @{T_args} ncontent) Z.cat
    val dest_ncontent : (@{ParaT_args}, @{T_args} ncontent, @{T_args} Z.ZO.content) Z.cat
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    where type @{T_args} ZM.container = @{T_args} Z.ZM.container
    where type @{T_args} ZO.content = @{T_args} ncontent
    where type @{T_args} ZO.zcontext = @{T_args} Z.ZO.zcontext
    where type @{T_args} zipper = @{T_args} Z.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZM = Z.ZM
  structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Optics_Content"\<close>(
    structure A = Kleisli_Arrow(Z.M)
    structure Z = Z.ZO
    type @{T_args} ncontent = @{T_args} ncontent
    val ncontent = ncontent
    val dest_ncontent = dest_ncontent
  )
)
