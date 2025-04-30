(*  Title:      Zippy/extend_zipper_context.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "EXTEND_ZIPPER_CONTEXT"\<close> =
sig
  structure Zbase : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  type @{AllT_args} new_zcontext

  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} Zbase.ZM.container * @{AllT_args} new_zcontext
  sharing type ZD.content = Zbase.ZD.content
  sharing type ZD.L.lens = Zbase.ZD.L.lens
  sharing type M.t = Zbase.M.t

  val mk_zcontext : (@{ParaT_args} @{AllT_args} Zbase.ZD.zcontext * @{AllT_args} new_zcontext,
    @{AllT_args} ZD.zcontext) cat

  val get_base_zcontext : (@{ParaT_args} @{AllT_args} ZD.zcontext,
    @{AllT_args} Zbase.ZD.zcontext) ZD.L.getter
  val get_new_zcontext : (@{ParaT_args} @{AllT_args} ZD.zcontext, @{AllT_args} new_zcontext) ZD.L.getter

  val zipper_from_base_zipper : (@{ParaT_args} @{AllT_args} Zbase.zipper * @{AllT_args} new_zcontext,
    @{AllT_args} zipper) cat
  val base_zipper_from_zipper : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} Zbase.zipper) cat
end

functor \<^eval>\<open>sfx_T_nargs "Extend_Zipper_Context"\<close>(
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD.content = Z.ZD.content
    sharing type ZD.L.lens = Z.ZD.L.lens
    sharing type ZD.L.K.M.t = Z.M.t
    type @{AllT_args} new_zcontext
    val mk_zcontext : (@{ParaT_args} @{AllT_args} Z.ZD.zcontext * @{AllT_args} new_zcontext,
      @{AllT_args} ZD.zcontext) Z.cat
    val get_base_zcontext : (@{ParaT_args} @{AllT_args} ZD.zcontext,
      @{AllT_args} Z.ZD.zcontext) Z.ZD.L.getter
    val get_new_zcontext : (@{ParaT_args} @{AllT_args} ZD.zcontext,
      @{AllT_args} new_zcontext) Z.ZD.L.getter
  ) :
    \<^eval>\<open>sfx_T_nargs "EXTEND_ZIPPER_CONTEXT"\<close>
    where type @{AllT_args} zipper = @{AllT_args} ZD.zipper
  =
struct

structure Zbase = Z
type @{AllT_args} new_zcontext = @{AllT_args} new_zcontext
val mk_zcontext = mk_zcontext
val get_base_zcontext = get_base_zcontext
val get_new_zcontext = get_new_zcontext

local
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(Z)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z.M)
  open SC A
in

fun zipper_from_base_zipper x = x |>
  (first (Z.ZD.CO.getter &&& Z.ZD.ZCTXT.getter)
  >>> arr (fn ((content, base_zctxt), new_zctxt) => (content, (base_zctxt, new_zctxt)))
  >>> second mk_zcontext
  >>> ZD.zipper)

fun base_zipper_from_zipper x = x |>
  (ZD.CO.getter &&& (ZD.ZCTXT.getter >>> get_base_zcontext)
  >>> Z.ZD.zipper)

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZD = ZD
  structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
    type @{AllT_args} content = @{AllT_args} Z.ZD.content
    type @{AllT_args} zcontext = @{AllT_args} ZD.zcontext
    type @{AllT_args} zipper = @{AllT_args} ZD.zipper
    structure ZM = Z.ZM
    structure M = ZM
    type @{AllT_args} container = @{AllT_args} ZM.container * @{AllT_args} new_zcontext
    fun zip x = x |> (first ZM.Zip.move >>> zipper_from_base_zipper)
    fun unzip x = x |>
      ((base_zipper_from_zipper >>> ZM.Unzip.move) &&& (ZD.ZCTXT.getter >>> get_new_zcontext))
    fun lift_move move =
      (base_zipper_from_zipper >>> move) &&& (ZD.ZCTXT.getter >>> get_new_zcontext)
      >>> zipper_from_base_zipper
    fun up x = x |> lift_move ZM.Up.move
    fun down x = x |> lift_move ZM.Down.move
    fun left x = x |> lift_move ZM.Left.move
    fun right x = x |> lift_move ZM.Right.move)
)
open Z

end

end
