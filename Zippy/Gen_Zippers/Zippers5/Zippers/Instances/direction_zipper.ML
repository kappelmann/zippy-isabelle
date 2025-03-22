(*  Title:      Zippy/direction_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Direction_Zipper"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) M.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZO.content = Zipper_Direction.direction
    where type @{AllT_args} ZO.zcontext = unit
    where type @{AllT_args} ZM.container = Zipper_Direction.direction
    where type @{AllT_args} ZM.zipper = Zipper_Direction.direction
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) M.K.M.t
  =
\<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  structure M = M
  structure L = L
  type @{AllT_args} container = Zipper_Direction.direction
  type @{AllT_args} content = Zipper_Direction.direction
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M.M) open A
  fun zip x = x |> K Zipper_Direction.Zip
  fun unzip x = x |> K Zipper_Direction.Unzip
  fun up x = x |> K Zipper_Direction.Up
  fun down x = x |> K Zipper_Direction.Down
  fun left x = x |> K Zipper_Direction.Left
  fun right x = x |> K Zipper_Direction.Right
)
