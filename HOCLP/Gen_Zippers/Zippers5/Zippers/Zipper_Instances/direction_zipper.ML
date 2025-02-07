(*  Title:      HOCLP/direction_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Direction_Zipper"\<close>(
    structure M : MOVE_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) M.cat
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    where type @{T_args} ZO.content = Zipper_Direction.direction
    where type @{T_args} ZO.zcontext = unit
    where type @{T_args} ZM.container = Zipper_Direction.direction
    where type @{T_args} ZM.zipper = Zipper_Direction.direction
    where type ('p1, 'a) M.t = ('p1, 'a) M.K.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper"\<close>(
  structure M = M
  structure L = L
  type @{T_args} content = Zipper_Direction.direction
  structure A = Kleisli_Arrow(M.M) open A
  fun zip x = x |> K Zipper_Direction.Zip
  fun unzip x = x |> K Zipper_Direction.Unzip
  fun up x = x |> K Zipper_Direction.Up
  fun down x = x |> K Zipper_Direction.Down
  fun left x = x |> K Zipper_Direction.Left
  fun right x = x |> K Zipper_Direction.Right
)
