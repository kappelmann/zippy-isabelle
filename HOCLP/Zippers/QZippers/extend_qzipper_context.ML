(*  Title:      HOCLP/extend_qzipper_context.ML
    Author:     Kevin Kappelmann
*)
signature EXTEND_QZIPPER_CONTEXT =
sig
  structure Z : QZIPPER
  type ('i, 'a, 'b, 'c, 'd) new_zcontext

  include QZIPPER
  where type ('i, 'a, 'b, 'c, 'd) container =
    ('i, 'a, 'b, 'c, 'd) Z.container * ('i, 'a, 'b, 'c, 'd) new_zcontext
  sharing type content = Z.content
  sharing type cat = Z.cat

  val mk_zcontext : ('i, 'a, 'b, 'c, 'd) Z.zcontext -> ('i, 'a, 'b, 'c, 'd) new_zcontext ->
    ('i, 'a, 'b, 'c, 'd) zcontext
  val get_old_zcontext : ('i, 'a, 'b, 'c, 'd) zcontext -> ('i, 'a, 'b, 'c, 'd) Z.zcontext
  val get_new_zcontext : ('i, 'a, 'b, 'c, 'd) zcontext -> ('i, 'a, 'b, 'c, 'd) new_zcontext

  val zipper_from_old_zipper : ('i, 'a, 'b, 'c, 'd) new_zcontext -> ('i, 'a, 'b, 'c, 'd) Z.zipper ->
    ('i, 'a, 'b, 'c, 'd) zipper
  val old_zipper_from_zipper : ('i, 'a, 'b, 'c, 'd) zipper -> ('i, 'a, 'b, 'c, 'd) Z.zipper

  val lift_move : ('i, ('i, 'a, 'b, 'c, 'd) Z.zipper) Z.hom_move ->
    ('i, ('i, 'a, 'b, 'c, 'd) zipper) hom_move
end

functor Extend_QZipper_Context(
    structure ZD : ZIPPER_DATA
    structure A : LAZY_IARROW_BASE
    structure Z : QZIPPER
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
    type ('i, 'a, 'b, 'c, 'd) new_zcontext
    type ('i, 'a, 'b, 'c, 'd) zcontext
    val mk_zcontext : ('i, 'a, 'b, 'c, 'd) Z.zcontext -> ('i, 'a, 'b, 'c, 'd) new_zcontext ->
      ('i, 'a, 'b, 'c, 'd) zcontext
    val get_old_zcontext : ('i, 'a, 'b, 'c, 'd) zcontext -> ('i, 'a, 'b, 'c, 'd) Z.zcontext
    val get_new_zcontext : ('i, 'a, 'b, 'c, 'd) zcontext -> ('i, 'a, 'b, 'c, 'd) new_zcontext
  ) : EXTEND_QZIPPER_CONTEXT =
struct

structure Z = Z
type ('i, 'a, 'b, 'c, 'd) new_zcontext = ('i, 'a, 'b, 'c, 'd) new_zcontext
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

structure NZ = QZipper(
  structure Zin = Z
  structure M = Zin
  structure Z =
  struct
    type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) Z.content
    type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) zcontext
    type ('i, 'a, 'b, 'c, 'd) zipper =
      (('i, 'a, 'b, 'c, 'd) content, ('i, 'a, 'b, 'c, 'd) zcontext) ZD.zipper

    val zipper = ZD.zipper
    val get_content = ZD.get_content
    val get_zcontext = ZD.get_zcontext
    val map_content = ZD.map_content
    val map_zcontext = ZD.map_zcontext

    type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z.container * ('i, 'a, 'b, 'c, 'd) new_zcontext
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
