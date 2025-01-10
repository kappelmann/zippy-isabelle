(*  Title:      HOCLP/extend_zipper4_context.ML
    Author:     Kevin Kappelmann
*)
signature EXTEND_ZIPPER4_CONTEXT =
sig
  structure Zbase : ZIPPER4
  type ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext

  include ZIPPER4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container =
    ('p1, 'a1, 'a2, 'a3, 'a4) Zbase.ZM.container * ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext
  sharing type ZO.content = Zbase.ZO.content
  sharing type M.t = Zbase.M.t

  val mk_zcontext : ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) Zbase.ZO.zcontext * ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext,
    ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext) cat

  val get_base_zcontext : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext,
    ('p1, 'a1, 'a2, 'a3, 'a4) Zbase.ZO.zcontext) ZO.L.getter
  val get_new_zcontext : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext,
    ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext) ZO.L.getter

  val zipper_from_base_zipper : ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext * ('p1, 'a1, 'a2, 'a3, 'a4) Zbase.zipper,
    ('p1, 'a1, 'a2, 'a3, 'a4) zipper) cat
  val base_zipper_from_zipper : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zipper,
    ('p1, 'a1, 'a2, 'a3, 'a4) Zbase.zipper) cat
end

functor Extend_Zipper4_Context(
    structure Z : ZIPPER4
    type ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
    structure ZO : ZIPPER4_OPTICS
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z.cat
    val mk_zcontext : ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.zcontext * ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext,
      ('p1, 'a1, 'a2, 'a3, 'a4) zcontext) Z.cat
    val get_base_zcontext : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext,
      ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.zcontext) Z.ZO.L.getter
    val get_new_zcontext : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) zcontext,
      ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext) Z.ZO.L.getter
  ) :
    EXTEND_ZIPPER4_CONTEXT
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zipper
  =
struct

structure Zbase = Z
type ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext
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
  (ZO.get_content &&& ZO.get_zcontext
  >>> second get_base_zcontext
  >>> Z.ZO.zipper)

structure Z = Zipper4(
  structure ZO = ZO
  structure ZM = Zipper4_Moves(
    type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) Z.ZO.content
    type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) zcontext
    type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zipper
    structure Zin = Z.ZM
    structure M = Zin
    type ('p1, 'a1, 'a2, 'a3, 'a4) container =
      ('p1, 'a1, 'a2, 'a3, 'a4) Zin.container * ('p1, 'a1, 'a2, 'a3, 'a4) new_zcontext
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

