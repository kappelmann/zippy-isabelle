(*  Title:      HOCLP/extend_zipper5_context.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "EXTEND_ZIPPER" ^ "_CONTEXT"\<close> =
sig
  structure Zbase : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  type @{T_args} new_zcontext

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  where type @{T_args} ZM.container = @{T_args} Zbase.ZM.container * @{T_args} new_zcontext
  sharing type ZO.content = Zbase.ZO.content
  sharing type M.t = Zbase.M.t

  val mk_zcontext : (@{ParaT_args}, @{T_args} Zbase.ZO.zcontext * @{T_args} new_zcontext,
    @{T_args} ZO.zcontext) cat

  val get_base_zcontext : (@{ParaT_args}, @{T_args} ZO.zcontext,
    @{T_args} Zbase.ZO.zcontext) ZO.L.getter
  val get_new_zcontext : (@{ParaT_args}, @{T_args} ZO.zcontext, @{T_args} new_zcontext) ZO.L.getter

  val zipper_from_base_zipper : (@{ParaT_args}, @{T_args} new_zcontext * @{T_args} Zbase.zipper,
    @{T_args} zipper) cat
  val base_zipper_from_zipper : (@{ParaT_args}, @{T_args} zipper, @{T_args} Zbase.zipper) cat
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Extend_Zipper" ^ "_Context"\<close>(
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    type @{T_args} new_zcontext
    type @{T_args} zcontext
    structure ZO : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type @{T_args} content = @{T_args} Z.ZO.content
    where type @{T_args} zcontext = @{T_args} zcontext
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.cat
    val mk_zcontext : (@{ParaT_args}, @{T_args} Z.ZO.zcontext * @{T_args} new_zcontext,
      @{T_args} zcontext) Z.cat val get_base_zcontext : (@{ParaT_args}, @{T_args} zcontext,
      @{T_args} Z.ZO.zcontext) Z.ZO.L.getter
    val get_new_zcontext : (@{ParaT_args}, @{T_args} zcontext, @{T_args} new_zcontext) Z.ZO.L.getter
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "EXTEND_ZIPPER" ^ "_CONTEXT"\<close>
    where type @{T_args} ZO.zipper = @{T_args} ZO.zipper
  =
struct

structure Zbase = Z
type @{T_args} new_zcontext = @{T_args} new_zcontext
val mk_zcontext = mk_zcontext
val get_base_zcontext = get_base_zcontext
val get_new_zcontext = get_new_zcontext

local structure SC = Semi_Category(Z); structure A = Kleisli_Arrow(Z.M) open SC A
in

fun zipper_from_base_zipper x = x |>
  (second (Z.ZO.get_content &&& Z.ZO.get_zcontext)
  >>> arr (fn (new_zcontext, (content, base_zcontext)) => (content, (base_zcontext, new_zcontext)))
  >>> second mk_zcontext
  >>> ZO.zipper)

fun base_zipper_from_zipper x = x |>
  (ZO.get_content &&& (ZO.get_zcontext >>> get_base_zcontext)
  >>> Z.ZO.zipper)

structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZO = ZO
  structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
    type @{T_args} content = @{T_args} Z.ZO.content
    type @{T_args} zcontext = @{T_args} zcontext
    type @{T_args} zipper = @{T_args} ZO.zipper
    structure Zin = Z.ZM
    structure M = Zin
    type @{T_args} container = @{T_args} Zin.container * @{T_args} new_zcontext
    fun zip x = x |> (first Zin.Zip.move >>> arr swap >>> zipper_from_base_zipper)
    fun unzip x = x |>
      ((base_zipper_from_zipper >>> Zin.Unzip.move) &&& (ZO.get_zcontext >>> get_new_zcontext))
    fun lift_move move =
      (ZO.get_zcontext >>> get_new_zcontext) &&& (base_zipper_from_zipper >>> move)
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

