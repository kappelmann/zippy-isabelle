(*  Title:      HOCLP/alternating_qzippers_qzippers.ML
    Author:     Kevin Kappelmann
*)
functor Alternating_QZippers_QNodes_Base_Args_QZippers(
    structure Z1 : QZIPPER
    structure Z2 : QZIPPER
    structure Z3 : QZIPPER
    structure Z4 : QZIPPER
    type ('i, 'a, 'b, 'c, 'd) ncontent1 (*content for node1*)
    type ('i, 'a, 'b, 'c, 'd) ncontent2 (*content for node2*)
    type ('i, 'a, 'b, 'c, 'd) ncontent3 (*content for node3*)
    type ('i, 'a, 'b, 'c, 'd) ncontent4 (*content for node4*)
    val ncontent1 : ('i, 'a, 'b, 'c, 'd) Z1.content -> ('i, 'a, 'b, 'c, 'd) ncontent1
    val ncontent2 : ('i, 'a, 'b, 'c, 'd) Z2.content -> ('i, 'a, 'b, 'c, 'd) ncontent2
    val ncontent3 : ('i, 'a, 'b, 'c, 'd) Z3.content -> ('i, 'a, 'b, 'c, 'd) ncontent3
    val ncontent4 : ('i, 'a, 'b, 'c, 'd) Z4.content -> ('i, 'a, 'b, 'c, 'd) ncontent4
    val next1 : ('i, 'a, 'b, 'c, 'd) Z1.content ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z2.container) Z2.move
    val next2 : ('i, 'a, 'b, 'c, 'd) Z2.content ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z3.container) Z3.move
    val next3 : ('i, 'a, 'b, 'c, 'd) Z3.content ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z4.container) Z4.move
    val next4 : ('i, 'a, 'b, 'c, 'd) Z4.content ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z1.container) Z1.move
    val content1 : ('i, 'a, 'b, 'c, 'd) ncontent1 ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z2.container) Z2.move -> ('i, 'a, 'b, 'c, 'd) Z1.content
    val content2 : ('i, 'a, 'b, 'c, 'd) ncontent2 ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z3.container) Z3.move -> ('i, 'a, 'b, 'c, 'd) Z2.content
    val content3 : ('i, 'a, 'b, 'c, 'd) ncontent3 ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z4.container) Z4.move -> ('i, 'a, 'b, 'c, 'd) Z3.content
    val content4 : ('i, 'a, 'b, 'c, 'd) ncontent4 ->
      ('i, unit, ('i, 'b, 'c, 'd, 'a) Z1.container) Z1.move -> ('i, 'a, 'b, 'c, 'd) Z4.content
  ) :
    ALTERNATING_QZIPPERS_QNODES_BASE_ARGS
    where type ('i, 'a, 'b, 'c, 'd) Z1.zcontext = ('i, 'a, 'b, 'c, 'd) Z1.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z1.zipper = ('i, 'a, 'b, 'c, 'd) Z1.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z1.container = ('i, 'a, 'b, 'c, 'd) Z1.container
    where type ('i, 'a, 'b, 'c, 'd) Z2.zcontext = ('i, 'a, 'b, 'c, 'd) Z2.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z2.zipper = ('i, 'a, 'b, 'c, 'd) Z2.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z2.container = ('i, 'a, 'b, 'c, 'd) Z2.container
    where type ('i, 'a, 'b, 'c, 'd) Z3.zcontext = ('i, 'a, 'b, 'c, 'd) Z3.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z3.zipper = ('i, 'a, 'b, 'c, 'd) Z3.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z3.container = ('i, 'a, 'b, 'c, 'd) Z3.container
    where type ('i, 'a, 'b, 'c, 'd) Z4.zcontext = ('i, 'a, 'b, 'c, 'd) Z4.zcontext
    where type ('i, 'a, 'b, 'c, 'd) Z4.zipper = ('i, 'a, 'b, 'c, 'd) Z4.zipper
    where type ('i, 'a, 'b, 'c, 'd) Z4.container = ('i, 'a, 'b, 'c, 'd) Z4.container
    where type ('i, 'a, 'b, 'c, 'd) N1.content = ('i, 'a, 'b, 'c, 'd) ncontent1
    where type ('i, 'a, 'b, 'c, 'd) N2.content = ('i, 'a, 'b, 'c, 'd) ncontent2
    where type ('i, 'a, 'b, 'c, 'd) N3.content = ('i, 'a, 'b, 'c, 'd) ncontent3
    where type ('i, 'a, 'b, 'c, 'd) N4.content = ('i, 'a, 'b, 'c, 'd) ncontent4
  =
struct
  structure N1 = QNode(
    type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent1
    type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z2.container) Z2.Init.move
  )
  structure N2 = QNode(
    type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent2
    type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z3.container) Z3.Init.move
  )
  structure N3 = QNode(
    type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent3
    type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z4.container) Z4.Init.move
  )
  structure N4 = QNode(
    type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) ncontent4
    type ('i, 'a, 'b, 'c, 'd) next = ('i, unit, ('i, 'b, 'c, 'd, 'a) Z1.container) Z1.Init.move
  )
  structure Z1 = Replace_QZipper_Content(
    structure Z = Z1
    type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N1.node
    fun ncontent x = N1.node (ncontent1 x) (next1 x)
    fun dest_ncontent x = N1.dest_node x |> (fn {content, next} => content1 content next)
  )
  structure Z2 = Replace_QZipper_Content(
    structure Z = Z2
    type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N2.node
    fun ncontent x = N2.node (ncontent2 x) (next2 x)
    fun dest_ncontent x = N2.dest_node x |> (fn {content, next} => content2 content next)
  )
  structure Z3 = Replace_QZipper_Content(
    structure Z = Z3
    type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N3.node
    fun ncontent x = N3.node (ncontent3 x) (next3 x)
    fun dest_ncontent x = N3.dest_node x |> (fn {content, next} => content3 content next)
  )
  structure Z4 = Replace_QZipper_Content(
    structure Z = Z4
    type ('i, 'a, 'b, 'c, 'd) ncontent = ('i, 'a, 'b, 'c, 'd) N4.node
    fun ncontent x = N4.node (ncontent4 x) (next4 x)
    fun dest_ncontent x = N4.dest_node x |> (fn {content, next} => content4 content next)
  )
end
