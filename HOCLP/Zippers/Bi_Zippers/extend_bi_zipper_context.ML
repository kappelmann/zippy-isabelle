(*  Title:      HOCLP/extend_bi_zipper_context.ML
    Author:     Kevin Kappelmann
*)
signature EXTEND_BI_ZIPPER_CONTEXT =
sig
  structure Z : BI_ZIPPER
  type ('i, 'a, 'b) new_zcontext

  include BI_ZIPPER
  where type ('i, 'a, 'b) container = ('i, 'a, 'b) Z.container * ('i, 'a, 'b) new_zcontext
  sharing type content = Z.content
  sharing type T.cat = Z.T.cat

  val mk_zcontext : ('i, 'a, 'b) Z.zcontext -> ('i, 'a, 'b) new_zcontext -> ('i, 'a, 'b) zcontext
  val get_old_zcontext : ('i, 'a, 'b) zcontext -> ('i, 'a, 'b) Z.zcontext
  val get_new_zcontext : ('i, 'a, 'b) zcontext -> ('i, 'a, 'b) new_zcontext

  val zipper_from_old_zipper : ('i, 'a, 'b) new_zcontext -> ('i, 'a, 'b) Z.zipper -> ('i, 'a, 'b) zipper
  val old_zipper_from_zipper : ('i, 'a, 'b) zipper -> ('i, 'a, 'b) Z.zipper

  val lift_move : ('i, ('i, 'a, 'b) Z.zipper) Z.hom_move -> ('i, ('i, 'a, 'b) zipper) hom_move
end

functor Extend_Bi_Zipper_Context(
    structure ZD : ZIPPER_DATA
    structure A : LAZY_IARROW_BASE
    structure Z : BI_ZIPPER
    sharing type Z.T.cat = A.T.cat
    type ('i, 'a, 'b) new_zcontext
    type ('i, 'a, 'b) zcontext
    val mk_zcontext : ('i, 'a, 'b) Z.zcontext -> ('i, 'a, 'b) new_zcontext -> ('i, 'a, 'b) zcontext
    val get_old_zcontext : ('i, 'a, 'b) zcontext -> ('i, 'a, 'b) Z.zcontext
    val get_new_zcontext : ('i, 'a, 'b) zcontext -> ('i, 'a, 'b) new_zcontext
  ) : EXTEND_BI_ZIPPER_CONTEXT =
struct

structure Z = Z
type ('i, 'a, 'b) new_zcontext = ('i, 'a, 'b) new_zcontext
val mk_zcontext = mk_zcontext
val get_old_zcontext = get_old_zcontext
val get_new_zcontext = get_new_zcontext

fun zipper_from_old_zipper new_zcontext old_zipper =
  let
    val content = Z.get_content old_zipper
    val old_zcontext = Z.get_zcontext old_zipper
    val zcontext = mk_zcontext old_zcontext new_zcontext
    val zipper = ZD.zipper content zcontext
  in zipper end

fun old_zipper_from_zipper zipper =
  let val {content, zcontext} = ZD.dest_zipper zipper
  in Z.zipper content (get_old_zcontext zcontext) end


local
structure A = IArrow(A)
structure C = ISemi_Category(A) open C
in
fun lift_move move =
  let val mk_zipper = ZD.get_zcontext #> get_new_zcontext #> zipper_from_old_zipper
  in
    A.&&& (A.arr mk_zipper, A.comp move (A.arr old_zipper_from_zipper))
    >>> A.arr SArrow_Apply.app
  end

structure NZ = Bi_Zipper(
  structure Zin = Z
  structure M = Zin
  structure Z =
  struct
    type ('i, 'a, 'b) content = ('i, 'a, 'b) Z.content
    type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) zcontext
    type ('i, 'a, 'b) zipper = (('i, 'a, 'b) content, ('i, 'a, 'b) zcontext) ZD.zipper

    val zipper = ZD.zipper
    val get_content = ZD.get_content
    val get_zcontext = ZD.get_zcontext
    val map_content = ZD.map_content
    val map_zcontext = ZD.map_zcontext

    type ('i, 'a, 'b) container = ('i, 'a, 'b) Z.container * ('i, 'a, 'b) new_zcontext
    structure SA = Arrow(SArrow_Apply)
    fun unzip zipper =
      SA.&&& (old_zipper_from_zipper #> Z.unzip, ZD.get_zcontext #> get_new_zcontext) zipper
  end
  fun init _ = (A.*** (Zin.Init.move, A.arr zipper_from_old_zipper) >>> A.arr (fn (x, f) => f x)) ()
  fun up _ = lift_move Zin.Up.move ()
  fun down _ = lift_move Zin.Down.move ()
  fun left _ = lift_move Zin.Left.move ()
  fun right _ = lift_move Zin.Right.move ()
)
end
open NZ

end
