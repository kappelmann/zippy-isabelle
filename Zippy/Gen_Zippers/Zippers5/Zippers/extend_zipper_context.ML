(*  Title:      Zippy/extend_zipper5_context.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "EXTEND_ZIPPER_CONTEXT"\<close> =
sig
  structure Zbase : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  type @{AllT_args} new_zcontext

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} Zbase.ZM.container * @{AllT_args} new_zcontext
  sharing type ZO.content = Zbase.ZO.content
  sharing type M.t = Zbase.M.t

  val mk_zcontext : (@{ParaT_args} @{AllT_args} Zbase.ZO.zcontext * @{AllT_args} new_zcontext,
    @{AllT_args} ZO.zcontext) cat

  val get_base_zcontext : (@{ParaT_args} @{AllT_args} ZO.zcontext,
    @{AllT_args} Zbase.ZO.zcontext) ZO.L.getter
  val get_new_zcontext : (@{ParaT_args} @{AllT_args} ZO.zcontext, @{AllT_args} new_zcontext) ZO.L.getter

  val zipper_from_base_zipper : (@{ParaT_args} @{AllT_args} Zbase.zipper * @{AllT_args} new_zcontext,
    @{AllT_args} zipper) cat
  val base_zipper_from_zipper : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} Zbase.zipper) cat
end

functor \<^eval>\<open>sfx_T_nargs "Extend_Zipper_Context"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    type @{AllT_args} new_zcontext
    type @{AllT_args} zcontext
    structure ZO : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type @{AllT_args} content = @{AllT_args} Z.ZO.content
    where type @{AllT_args} zcontext = @{AllT_args} zcontext
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) Z.cat
    val mk_zcontext : (@{ParaT_args} @{AllT_args} Z.ZO.zcontext * @{AllT_args} new_zcontext,
      @{AllT_args} zcontext) Z.cat val get_base_zcontext : (@{ParaT_args} @{AllT_args} zcontext,
      @{AllT_args} Z.ZO.zcontext) Z.ZO.L.getter
    val get_new_zcontext : (@{ParaT_args} @{AllT_args} zcontext, @{AllT_args} new_zcontext) Z.ZO.L.getter
  ) :
    \<^eval>\<open>sfx_T_nargs "EXTEND_ZIPPER_CONTEXT"\<close>
    where type @{AllT_args} ZO.zipper = @{AllT_args} ZO.zipper
  =
struct

structure Zbase = Z
type @{AllT_args} new_zcontext = @{AllT_args} new_zcontext
val mk_zcontext = mk_zcontext
val get_base_zcontext = get_base_zcontext
val get_new_zcontext = get_new_zcontext

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z.M) open SC A
in

fun zipper_from_base_zipper x = x |>
  (first (Z.ZO.get_content &&& Z.ZO.get_zcontext)
  >>> arr (fn ((content, base_zcontext), new_zcontext) => (content, (base_zcontext, new_zcontext)))
  >>> second mk_zcontext
  >>> ZO.zipper)

fun base_zipper_from_zipper x = x |>
  (ZO.get_content &&& (ZO.get_zcontext >>> get_base_zcontext)
  >>> Z.ZO.zipper)

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZO = ZO
  structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
    type @{AllT_args} content = @{AllT_args} Z.ZO.content
    type @{AllT_args} zcontext = @{AllT_args} zcontext
    type @{AllT_args} zipper = @{AllT_args} ZO.zipper
    structure Zin = Z.ZM
    structure M = Zin
    type @{AllT_args} container = @{AllT_args} Zin.container * @{AllT_args} new_zcontext
    fun zip x = x |> (first Zin.Zip.move >>> zipper_from_base_zipper)
    fun unzip x = x |>
      ((base_zipper_from_zipper >>> Zin.Unzip.move) &&& (ZO.get_zcontext >>> get_new_zcontext))
    fun lift_move move =
      (base_zipper_from_zipper >>> move) &&& (ZO.get_zcontext >>> get_new_zcontext)
      >>> zipper_from_base_zipper
    fun up x = x |> lift_move Zin.Up.move
    fun down x = x |> lift_move Zin.Down.move
    fun left x = x |> lift_move Zin.Left.move
    fun right x = x |> lift_move Zin.Right.move
  )
)
open Z

end

end
