(*  Title:      HOCLP/alternating_zippers4_simple_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Alternating_Zippers4_Nodes_Base_Args_Simple_Zippers(
    structure Z1 : ZIPPER4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = 'a1
    structure Z2 : ZIPPER4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = 'a1
    where type ('p1, 't, 'o, 's, 'i) ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
    sharing type Z2.M.t = Z1.M.t
    structure Z3 : ZIPPER4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = 'a1
    where type ('p1, 't, 'o, 's, 'i) ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
    sharing type Z3.M.t = Z1.M.t
    structure Z4 : ZIPPER4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = 'a1
    where type ('p1, 't, 'o, 's, 'i) ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
    sharing type Z4.M.t = Z1.M.t
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1 (*content for node1*)
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2 (*content for node2*)
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3 (*content for node3*)
    type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4 (*content for node4*)
  ) :
  sig
    type ('p1, 'a1, 'a2, 'a3, 'a4) node1
    type ('p1, 'a1, 'a2, 'a3, 'a4) node2
    type ('p1, 'a1, 'a2, 'a3, 'a4) node3
    type ('p1, 'a1, 'a2, 'a3, 'a4) node4

    include ALTERNATING_ZIPPERS4_NODES_BASE_ARGS
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container =
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node1, 'a2, 'a3, 'a4) Z1.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container =
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node2, 'a2, 'a3, 'a4) Z2.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container =
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node3, 'a2, 'a3, 'a4) Z3.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container =
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) node4, 'a2, 'a3, 'a4) Z4.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N1.node = ('p1, 'a1, 'a2, 'a3, 'a4) node1
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N2.node = ('p1, 'a1, 'a2, 'a3, 'a4) node2
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N3.node = ('p1, 'a1, 'a2, 'a3, 'a4) node3
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N4.node = ('p1, 'a1, 'a2, 'a3, 'a4) node4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N1.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N2.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N3.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3
    where type ('p1, 'a1, 'a2, 'a3, 'a4) N4.content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4
    (* where ('p1, 'a1, 'a2, 'a3, 'a4) Zi.ZO.zcontext =
      ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Ni.node, 'a2, 'a3, 'a4) Zi.ZO.zcontext *)
    where type ('p1, 'a) Z1.M.t = ('p1, 'a) Z1.M.t
    where type ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
  end
  =
struct

structure Base = struct type ('p1, 'a1, 'a2, 'a3, 'a4, 'n) next = 'n end
structure N1 = Node5(open Base type ('p1, 'a1, 'a2, 'a3, 'a4, 'n) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1)
structure N2 = Node5(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'n) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2)
structure N3 = Node5(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'n) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3)
structure N4 = Node5(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'n) content = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4)
structure A = Kleisli_Arrow(Z1.M)
structure Base = struct structure AF = SArrow_Arrow_Apply.A; structure AT = A; structure L = Z1.ZO.L;
  fun lift a = AT.arr a end
structure N1 = Lift_Node5(open Base; structure N = N1)
structure N2 = Lift_Node5(open Base; structure N = N2)
structure N3 = Lift_Node5(open Base; structure N = N3)
structure N4 = Lift_Node5(open Base; structure N = N4)

datatype ('p1, 'a1, 'a2, 'a3, 'a4) next1 = Next1 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, ('p1, 'a1, 'a2, 'a3, 'a4) next2) N2.node, 'a2, 'a3, 'a4)
    Z2.ZM.container) Z2.ZM.Zip.M.t
and ('p1, 'a1, 'a2, 'a3, 'a4) next2 = Next2 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, ('p1, 'a1, 'a2, 'a3, 'a4) next3) N3.node, 'a2, 'a3, 'a4)
    Z3.ZM.container) Z3.ZM.Zip.M.t
and ('p1, 'a1, 'a2, 'a3, 'a4) next3 = Next3 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, ('p1, 'a1, 'a2, 'a3, 'a4) next4) N4.node, 'a2, 'a3, 'a4)
    Z4.ZM.container) Z4.ZM.Zip.M.t
and ('p1, 'a1, 'a2, 'a3, 'a4) next4 = Next4 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, ('p1, 'a1, 'a2, 'a3, 'a4) next1) N1.node, 'a2, 'a3, 'a4)
    Z1.ZM.container) Z1.ZM.Zip.M.t

fun next1 x = Next1 x
fun dest_next1 (Next1 x) = x
fun next2 x = Next2 x
fun dest_next2 (Next2 x) = x
fun next3 x = Next3 x
fun dest_next3 (Next3 x) = x
fun next4 x = Next4 x
fun dest_next4 (Next4 x) = x

structure Base =
struct
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst1 = 'a1
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst2 = 'a2
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst3 = 'a3
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst4 = 'a4
end
structure N1 = Node4_Node5(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst5 = ('p1, 'a1, 'a2, 'a3, 'a4) next1
  structure N = N1)
structure N2 = Node4_Node5(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst5 = ('p1, 'a1, 'a2, 'a3, 'a4) next2
  structure N = N2)
structure N3 = Node4_Node5(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst5 = ('p1, 'a1, 'a2, 'a3, 'a4) next3
  structure N = N3)
structure N4 = Node4_Node5(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst5 = ('p1, 'a1, 'a2, 'a3, 'a4) next4
  structure N = N4)

structure Base =
struct
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst2 = 'a2
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst3 = 'a3
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst4 = 'a4
end
structure Z1 = Instantiate_Zipper4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst1 = ('p1, 'a1, 'a2, 'a3, 'a4) N1.node
  structure Z = Z1)
structure Z2 = Instantiate_Zipper4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst1 = ('p1, 'a1, 'a2, 'a3, 'a4) N2.node
  structure Z = Z2)
structure Z3 = Instantiate_Zipper4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst1 = ('p1, 'a1, 'a2, 'a3, 'a4) N3.node
  structure Z = Z3)
structure Z4 = Instantiate_Zipper4(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4) inst1 = ('p1, 'a1, 'a2, 'a3, 'a4) N4.node
  structure Z = Z4)

structure Base =
struct
  structure A = A
  fun ncontent x = x |> A.id ()
  fun dest_ncontent x = x |> A.id ()
end
structure N1 = Replace_Node4_Content_Next(
  open Base
  structure N = N1
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent1
  type ('p1, 'a1, 'a2, 'a3, 'a4) nnext = ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) Z2.ZM.container) Z2.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next1
  fun dest_nnext x = x |> A.arr next1
)
structure N2 = Replace_Node4_Content_Next(
  open Base
  structure N = N2
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent2
  type ('p1, 'a1, 'a2, 'a3, 'a4) nnext = ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) Z3.ZM.container) Z3.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next2
  fun dest_nnext x = x |> A.arr next2
)
structure N3 = Replace_Node4_Content_Next(
  open Base
  structure N = N3
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent3
  type ('p1, 'a1, 'a2, 'a3, 'a4) nnext = ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) Z4.ZM.container) Z4.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next3
  fun dest_nnext x = x |> A.arr next3

)
structure N4 = Replace_Node4_Content_Next(
  open Base
  structure N = N4
  type ('p1, 'a1, 'a2, 'a3, 'a4) ncontent = ('p1, 'a1, 'a2, 'a3, 'a4) ncontent4
  type ('p1, 'a1, 'a2, 'a3, 'a4) nnext = ('p1,
    ('p1, 'a1, 'a2, 'a3, 'a4) Z1.ZM.container) Z1.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next4
  fun dest_nnext x = x |> A.arr next4
)

type ('p1, 'a1, 'a2, 'a3, 'a4) node1 = ('p1, 'a1, 'a2, 'a3, 'a4) N1.node
type ('p1, 'a1, 'a2, 'a3, 'a4) node2 = ('p1, 'a1, 'a2, 'a3, 'a4) N2.node
type ('p1, 'a1, 'a2, 'a3, 'a4) node3 = ('p1, 'a1, 'a2, 'a3, 'a4) N3.node
type ('p1, 'a1, 'a2, 'a3, 'a4) node4 = ('p1, 'a1, 'a2, 'a3, 'a4) N4.node

end