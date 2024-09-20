(*  Title:      HOCLP/pair_bi_zipper.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_BI_ZIPPER_BASE =
sig
structure Z1 : BI_ZIPPER_BASE
structure Z2 : BI_ZIPPER_BASE

include BI_ZIPPER_BASE
where type ('i, 'a, 'b) content = ('i, 'a, 'b) Z1.content * ('i, 'a, 'b) Z2.content
where type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) Z1.zcontext * ('i, 'a, 'b) Z2.zcontext
where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) Z1.zipper * ('i, 'a, 'b) Z2.zipper
where type ('i, 'a, 'b) container = ('i, 'a, 'b) Z1.container * ('i, 'a, 'b) Z2.container
end

functor Pair_Bi_Zipper_Base(
  structure Z1 : BI_ZIPPER_BASE
  structure Z2 : BI_ZIPPER_BASE
  ) : PAIR_BI_ZIPPER_BASE =
struct

structure Z1 = Z1
structure Z2 = Z2

type ('i, 'a, 'b) content = ('i, 'a, 'b) Z1.content * ('i, 'a, 'b) Z2.content
type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) Z1.zcontext * ('i, 'a, 'b) Z2.zcontext
type ('i, 'a, 'b) zipper = ('i, 'a, 'b) Z1.zipper * ('i, 'a, 'b) Z2.zipper

local val op *** = SArrow_Apply.***
in
fun zipper (c1, c2) = Z1.zipper c1 *** Z2.zipper c2

fun get_content x = x |> (Z1.get_content *** Z2.get_content)
fun get_zcontext x = x |> (Z1.get_zcontext *** Z2.get_zcontext)

fun get_map get map1 map2 f z =
  let val (x1, x2) = get z |> f
  in (map1 (K x1) *** map2 (K x2)) z end

fun map_content x = x |> get_map get_content Z1.map_content Z2.map_content
fun map_zcontext x = x |> get_map get_zcontext Z1.map_zcontext Z2.map_zcontext

type ('i, 'a, 'b) container = ('i, 'a, 'b) Z1.container * ('i, 'a, 'b) Z2.container

fun unzip x = x |> (Z1.unzip *** Z2.unzip)
end
end

signature PAIR_BI_ZIPPER =
sig
  structure Z1 : BI_ZIPPER
  structure Z2 : BI_ZIPPER
  sharing type Z2.T.cat = Z1.T.cat

  include BI_ZIPPER
  where type ('i, 'a, 'b) content = ('i, 'a, 'b) Z1.content * ('i, 'a, 'b) Z2.content
  where type ('i, 'a, 'b) zcontext = ('i, 'a, 'b) Z1.zcontext * ('i, 'a, 'b) Z2.zcontext
  where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) Z1.zipper * ('i, 'a, 'b) Z2.zipper
  where type ('i, 'a, 'b) container = ('i, 'a, 'b) Z1.container * ('i, 'a, 'b) Z2.container
end

functor Pair_Bi_Zipper(
  structure A : LAZY_IARROW_BASE
  structure Z1 : BI_ZIPPER
  sharing type Z1.T.cat = A.T.cat
  structure Z2 : BI_ZIPPER
  sharing type Z2.T.cat = Z1.T.cat
  ) : PAIR_BI_ZIPPER =
struct

structure Z1 = Z1
structure Z2 = Z2

structure ZM = Pair_Bi_Zipper_Moves(structure A = A;structure M1 = Z1; structure M2 = Z2)

structure Z = Bi_Zipper(
  structure Z = Pair_Bi_Zipper_Base(structure Z1 = Z1; structure Z2 = Z2)
  structure M = ZM
  val init = ZM.Init.move
  val up = ZM.Up.move
  val down = ZM.Down.move
  val left = ZM.Left.move
  val right = ZM.Right.move
)
open Z

end
