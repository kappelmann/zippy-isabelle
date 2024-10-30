(*  Title:      HOCLP/pair_qzipper.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_QZIPPER_BASE =
sig
  structure Z1 : QZIPPER_BASE
  structure Z2 : QZIPPER_BASE

  include QZIPPER_BASE
  where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) Z1.content * ('i, 'a, 'b, 'c, 'd) Z2.content
  where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z1.zcontext * ('i, 'a, 'b, 'c, 'd) Z2.zcontext
  where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) Z1.zipper * ('i, 'a, 'b, 'c, 'd) Z2.zipper
  where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z1.container * ('i, 'a, 'b, 'c, 'd) Z2.container
end

functor Pair_QZipper_Base(
  structure Z1 : QZIPPER_BASE
  structure Z2 : QZIPPER_BASE
  ) : PAIR_QZIPPER_BASE =
struct

structure Z1 = Z1
structure Z2 = Z2

type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) Z1.content * ('i, 'a, 'b, 'c, 'd) Z2.content
type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z1.zcontext * ('i, 'a, 'b, 'c, 'd) Z2.zcontext
type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) Z1.zipper * ('i, 'a, 'b, 'c, 'd) Z2.zipper

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

type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z1.container * ('i, 'a, 'b, 'c, 'd) Z2.container

fun unzip x = x |> (Z1.unzip *** Z2.unzip)
end
end

signature PAIR_QZIPPER =
sig
  structure Z1 : QZIPPER
  structure Z2 : QZIPPER
  sharing type Z2.cat = Z1.cat

  include QZIPPER
  where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) Z1.content * ('i, 'a, 'b, 'c, 'd) Z2.content
  where type ('i, 'a, 'b, 'c, 'd) zcontext = ('i, 'a, 'b, 'c, 'd) Z1.zcontext * ('i, 'a, 'b, 'c, 'd) Z2.zcontext
  where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) Z1.zipper * ('i, 'a, 'b, 'c, 'd) Z2.zipper
  where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) Z1.container * ('i, 'a, 'b, 'c, 'd) Z2.container
end

functor Pair_QZipper(
  structure A : LAZY_IARROW_BASE
  structure Z1 : QZIPPER
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
  structure Z2 : QZIPPER
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) Z1.cat
  ) : PAIR_QZIPPER =
struct

structure Z1 = Z1
structure Z2 = Z2

structure ZM = Pair_QZipper_Moves(structure A = A;structure M1 = Z1; structure M2 = Z2)

structure Z = QZipper(
  structure Z = Pair_QZipper_Base(structure Z1 = Z1; structure Z2 = Z2)
  structure M = ZM
  val init = ZM.Init.move
  val up = ZM.Up.move
  val down = ZM.Down.move
  val left = ZM.Left.move
  val right = ZM.Right.move
)
open Z

end
