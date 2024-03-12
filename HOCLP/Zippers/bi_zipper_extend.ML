(*  Title:      HOCLP/bi_zipper_extend.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_BI_ZIPPER_MOVE =
sig
  structure ZM1 : BI_ZIPPER_MOVE
  structure ZM2 : BI_ZIPPER_MOVE
  sharing type ZM1.K.M.t = ZM2.K.M.t

  include BI_ZIPPER_MOVE
  where type ('a, 'b) from = ('a, 'b) ZM1.from * ('a, 'b) ZM2.from
  where type ('a, 'b) to = ('a, 'b) ZM1.to * ('a, 'b) ZM2.to
  sharing type ZM1.K.M.t = K.M.t
  sharing type ZM2.K.M.t = K.M.t
end

functor Pair_Bi_Zipper_Move(
    structure ZM1 : BI_ZIPPER_MOVE
    structure ZM2 : BI_ZIPPER_MOVE
    sharing type ZM1.K.M.t = ZM2.K.M.t
  ) : PAIR_BI_ZIPPER_MOVE =
struct

structure ZM1 = ZM1
structure ZM2 = ZM2

structure ZM = Zipper_Move_Base(ZM1.K)
open ZM

type ('a, 'b) from = ('a, 'b) ZM1.from * ('a, 'b) ZM2.from
type ('a, 'b) to = ('a, 'b) ZM1.to * ('a, 'b) ZM2.to

structure A = Kleisli_Arrow_Apply(ZM1.K.M)
fun move x = x |> A.*** ZM1.move ZM2.move

end

signature PAIR_BI_ZIPPER_MOVES =
sig
  structure ZM1 : BI_ZIPPER_MOVES
  structure ZM2 : BI_ZIPPER_MOVES

  include BI_ZIPPER_MOVES
  where type ('a, 'b) Init.from = ('a, 'b) ZM1.Init.from * ('a, 'b) ZM2.Init.from
  where type ('a, 'b) Init.to = ('a, 'b) ZM1.Init.to * ('a, 'b) ZM2.Init.to
  where type ('a, 'b) Up.from = ('a, 'b) ZM1.Up.from * ('a, 'b) ZM2.Up.from
  where type ('a, 'b) Up.to = ('a, 'b) ZM1.Up.to * ('a, 'b) ZM2.Up.to
  where type ('a, 'b) Down.from = ('a, 'b) ZM1.Down.from * ('a, 'b) ZM2.Down.from
  where type ('a, 'b) Down.to = ('a, 'b) ZM1.Down.to * ('a, 'b) ZM2.Down.to
  where type ('a, 'b) Left.from = ('a, 'b) ZM1.Left.from * ('a, 'b) ZM2.Left.from
  where type ('a, 'b) Left.to = ('a, 'b) ZM1.Left.to * ('a, 'b) ZM2.Left.to
  where type ('a, 'b) Right.from = ('a, 'b) ZM1.Right.from * ('a, 'b) ZM2.Right.from
  where type ('a, 'b) Right.to = ('a, 'b) ZM1.Right.to * ('a, 'b) ZM2.Right.to
  sharing type ZM1.K.M.t = K.M.t
  sharing type ZM2.K.M.t = K.M.t
end

functor Pair_Bi_Zipper_Moves(
    structure ZM1 : BI_ZIPPER_MOVES
    structure ZM2 : BI_ZIPPER_MOVES
    sharing type ZM1.K.M.t = ZM2.K.M.t
  ) : PAIR_BI_ZIPPER_MOVES =
struct

structure ZM1 = ZM1
structure ZM2 = ZM2

structure ZM = Zipper_Move_Base(ZM1.K)
open ZM

structure Init = Pair_Bi_Zipper_Move(structure ZM1 = ZM1.Init; structure ZM2 = ZM2.Init)
structure Up = Pair_Bi_Zipper_Move(structure ZM1 = ZM1.Up; structure ZM2 = ZM2.Up)
structure Down = Pair_Bi_Zipper_Move(structure ZM1 = ZM1.Down; structure ZM2 = ZM2.Down)
structure Left = Pair_Bi_Zipper_Move(structure ZM1 = ZM1.Left; structure ZM2 = ZM2.Left)
structure Right = Pair_Bi_Zipper_Move(structure ZM1 = ZM1.Right; structure ZM2 = ZM2.Right)

end

signature EXTEND_BI_ZIPPER_CONTEXT =
sig
  structure Z : BI_ZIPPER
  type ('c1, 'c2) new_zcontext

  include BI_ZIPPER
  where type ('c1, 'c2) container = ('c1, 'c2) Z.container * ('c1, 'c2) new_zcontext
  sharing type content = Z.content
  sharing type K.M.t = Z.K.M.t

  val zcontext : ('c1, 'c2) Z.zcontext -> ('c1, 'c2) new_zcontext -> ('c1, 'c2) zcontext
  val get_old_zcontext : ('c1, 'c2) zcontext -> ('c1, 'c2) Z.zcontext
  val get_new_zcontext : ('c1, 'c2) zcontext -> ('c1, 'c2) new_zcontext

  val zipper_from_old_zipper : ('c1, 'c2) new_zcontext -> ('c1, 'c2) Z.zipper -> ('c1, 'c2) zipper
  val old_zipper_from_zipper : ('c1, 'c2) zipper -> ('c1, 'c2) Z.zipper

  val lift_move : (('c1, 'c2) Z.zipper, ('c1, 'c2) Z.zipper) Z.move ->
    (('c1, 'c2) zipper, ('c1, 'c2) zipper) move
end

functor Extend_Bi_Zipper_Context(
    structure ZD : ZIPPER_DATA
    structure Z : BI_ZIPPER
    type ('c1, 'c2) new_zcontext
    type ('c1, 'c2) zcontext
    val zcontext : ('c1, 'c2) Z.zcontext -> ('c1, 'c2) new_zcontext -> ('c1, 'c2) zcontext
    val get_old_zcontext : ('c1, 'c2) zcontext -> ('c1, 'c2) Z.zcontext
    val get_new_zcontext : ('c1, 'c2) zcontext -> ('c1, 'c2) new_zcontext
  ) : EXTEND_BI_ZIPPER_CONTEXT =
struct

structure Z = Z
type ('c1, 'c2) new_zcontext = ('c1, 'c2) new_zcontext
val zcontext = zcontext
val get_old_zcontext = get_old_zcontext
val get_new_zcontext = get_new_zcontext

fun zipper_from_old_zipper more_context old_zipper =
  let
    val content = Z.get_content old_zipper
    val old_zcontext = Z.get_zcontext old_zipper
    val zcontext = zcontext old_zcontext more_context
    val zipper = ZD.zipper content zcontext
  in zipper end

fun old_zipper_from_zipper zipper =
  let val {content, zcontext} = ZD.dest_zipper zipper
  in Z.zipper content (get_old_zcontext zcontext) end

structure A = Kleisli_Arrow_Apply(Z.K.M)

fun lift_move move zipper =
  let val mk_zipper = ZD.get_zcontext zipper |> get_new_zcontext |> zipper_from_old_zipper
  in old_zipper_from_zipper zipper |> A.comp (A.arr mk_zipper) move end

structure NZ = Bi_Zipper(
  structure ZM = Z
  structure Z =
  struct
    type ('c1, 'c2) content = ('c1, 'c2) Z.content
    type ('c1, 'c2) zcontext = ('c1, 'c2) zcontext
    type ('c1, 'c2) zipper = (('c1, 'c2) content, ('c1, 'c2) zcontext) ZD.zipper

    val zipper = ZD.zipper
    val get_content = ZD.get_content
    val get_zcontext = ZD.get_zcontext
    val map_content = ZD.map_content
    val map_zcontext = ZD.map_zcontext

    type ('c1, 'c2) container = ('c1, 'c2) Z.container * ('c1, 'c2) new_zcontext
    structure SA = Arrow(SArrow_Apply)
    fun unzip zipper = zipper
      |> SA.&&& (old_zipper_from_zipper #> Z.unzip) (ZD.get_zcontext #> get_new_zcontext)
  end
  fun init (container, old_zipper) = container
    |> A.comp (A.arr (zipper_from_old_zipper old_zipper)) ZM.Init.move
  fun up zipper = lift_move ZM.Up.move zipper
  fun down zipper = lift_move ZM.Down.move zipper
  fun left zipper = lift_move ZM.Left.move zipper
  fun right zipper = lift_move ZM.Right.move zipper
)
open NZ

end

signature REPLACE_BI_ZIPPER_CONTAINER =
sig
  structure Z : BI_ZIPPER
  type ('c1, 'c2) ncontainer
  include BI_ZIPPER
  sharing type content = Z.content
  sharing type zcontext = Z.zcontext
  sharing type zipper = Z.zipper
  sharing type container = ncontainer
  sharing type K.M.t = Z.K.M.t
end

functor Replace_Bi_Zipper_Container(
    structure Z : BI_ZIPPER
    type ('c1, 'c2) ncontainer
    val ncontainer : ('c1, 'c2) Z.container -> ('c1, 'c2) ncontainer
    val dest_ncontainer : ('c1, 'c2) ncontainer -> ('c1, 'c2) Z.container
  ) : REPLACE_BI_ZIPPER_CONTAINER =
struct

structure Z = Z
type ('c1, 'c2) ncontainer = ('c1, 'c2) ncontainer

structure NZ = Bi_Zipper(
  structure ZM = Z
  structure Z =
  struct
    open Z
    type ('c1, 'c2) container = ('c1, 'c2) ncontainer
    fun unzip zipper = Z.unzip zipper |> ncontainer
  end
  fun init nc = dest_ncontainer nc |> Z.Init.move
  val up = Z.Up.move
  val down = Z.Down.move
  val left = Z.Left.move
  val right = Z.Right.move
)
open NZ

end