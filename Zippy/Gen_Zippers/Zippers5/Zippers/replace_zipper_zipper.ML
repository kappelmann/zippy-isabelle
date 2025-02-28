(*  Title:      HOCLP/replace_zipper_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Zipper"\<close>(
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    type @{T_args} nzipper
    val nzipper : (@{ParaT_args}, @{T_args} Z.zipper, @{T_args} nzipper) Z.cat
    val dest_nzipper : (@{ParaT_args}, @{T_args} nzipper, @{T_args} Z.zipper) Z.cat
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    where type @{T_args} ZM.container = @{T_args} Z.ZM.container
    where type @{T_args} ZO.content = @{T_args} Z.ZO.content
    where type @{T_args} ZO.zcontext = @{T_args} Z.ZO.zcontext
    where type @{T_args} zipper = @{T_args} nzipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure Base =
  struct
    type @{T_args} nzipper = @{T_args} nzipper
    val nzipper = nzipper
    val dest_nzipper = dest_nzipper
  end
  structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Moves_Zipper"\<close>(
    open Base; structure Z = Z.ZM)
  structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Optics_Zipper"\<close>(
    open Base; structure A = Kleisli_Arrow(Z.M); structure Z = Z.ZO)
)
