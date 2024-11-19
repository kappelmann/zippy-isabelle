(*  Title:      HOCLP/alternating_zippers4_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Alternating_Zippers4_Nodes_Base_Args_Zippers(
    structure A : LAZY_ARROW
    structure Z1 : ZIPPER4
    where type ('p1, 'a, 'b) ZM.cat = ('p1, 'a, 'b) A.cat
    structure Z2 : ZIPPER4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) Z1.cat
    where type ('p1, 't, 'o, 's, 'i) ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
    structure Z3 : ZIPPER4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) Z1.cat
    where type ('p1, 't, 'o, 's, 'i) ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
    structure Z4 : ZIPPER4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) Z1.cat
    where type ('p1, 't, 'o, 's, 'i) ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1 (*content for node1*)
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2 (*content for node2*)
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3 (*content for node3*)
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4 (*content for node4*)
    val ncontent1 : ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content -> ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1
    val ncontent2 : ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content -> ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2
    val ncontent3 : ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.content -> ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3
    val ncontent4 : ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.content -> ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4
    val next1 : ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container) Z2.move
    val next2 : ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container) Z3.move
    val next3 : ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.content ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container) Z4.move
    val next4 : ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.content ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container) Z1.move
    val content1 : ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1 ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container) Z2.move ->
        ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.content
    val content2 : ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2 ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container) Z3.move ->
        ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.content
    val content3 : ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3 ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container) Z4.move ->
      ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.content
    val content4 : ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4 ->
      ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container) Z1.move ->
      ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.content
  ) :
    ALTERNATING_ZIPPERS4_NODES_BASE_ARGS
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.zcontext = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper = ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N1.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N2.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N3.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N4.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4
    where type ('p1, 'a, 'b) Z1.cat = ('p1, 'a, 'b) Z1.cat
    where type ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
  =
struct
structure Base = struct structure A = A; structure L = Z1.ZO.L end
structure N1 = Node4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1
  type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container) Z2.ZM.Zip.move
)
structure N2 = Node4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2
  type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container) Z3.ZM.Zip.move
)
structure N3 = Node4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3
  type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container) Z4.ZM.Zip.move
)
structure N4 = Node4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4
  type ('p1, 'a1, 'a2, 'a3, 'a4) next =
    ('p1, unit, ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container) Z1.ZM.Zip.move
)
structure Base = struct structure A = A; open A end
structure Z1 = Replace_Zipper4_Content(
  open Base
  structure Z = Z1
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) N1.node
  fun ncontent _ = comp N1.node (arr ncontent1 &&& arr next1)
    |> Lazy_Cat_Util.unlift
  fun dest_ncontent _ = comp (arr (uncurry content1)) (N1.get_content &&& N1.get_next)
    |> Lazy_Cat_Util.unlift
)
structure Z2 = Replace_Zipper4_Content(
  open Base
  structure Z = Z2
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) N2.node
  fun ncontent _ = comp N2.node (arr ncontent2 &&& arr next2)
    |> Lazy_Cat_Util.unlift
  fun dest_ncontent _ = comp (arr (uncurry content2)) (N2.get_content &&& N2.get_next)
    |> Lazy_Cat_Util.unlift
)
structure Z3 = Replace_Zipper4_Content(
  open Base
  structure Z = Z3
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) N3.node
  fun ncontent _ = comp N3.node (arr ncontent3 &&& arr next3)
    |> Lazy_Cat_Util.unlift
  fun dest_ncontent _ = comp (arr (uncurry content3)) (N3.get_content &&& N3.get_next)
    |> Lazy_Cat_Util.unlift
)
structure Z4 = Replace_Zipper4_Content(
  open Base
  structure Z = Z4
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) N4.node
  fun ncontent _ = comp N4.node (arr ncontent4 &&& arr next4)
    |> Lazy_Cat_Util.unlift
  fun dest_ncontent _ = comp (arr (uncurry content4)) (N4.get_content &&& N4.get_next)
    |> Lazy_Cat_Util.unlift
)
end
