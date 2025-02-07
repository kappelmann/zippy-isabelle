(*  Title:      HOCLP/alternating_zippers_nodes_simple_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Alternating_Zippers5_Nodes_Base_Args_Simple_Zippers(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} : ZIPPER5
    where type @{T_args} ZO.content = @{PolyT_arg 0}
    sharing type Z{i}.ZO.L.lens = Z1.ZO.L.lens
    sharing type Z{i}.M.t = Z1.M.t\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{T_args} ncontent{i} (*content for node{i}*)\<close>\<close>
  ) :
  sig
    type @{T_args} node1
    type @{T_args} node2
    type @{T_args} node3
    type @{T_args} node4
    type @{T_args} node5

    include ALTERNATING_ZIPPERS5_NODES_BASE_ARGS
    where type @{T_args} Z1.ZM.container =
      ('p1, @{T_args} node1, 'a2, 'a3, 'a4, 'a5) Z1.ZM.container
    where type @{T_args} Z2.ZM.container =
      ('p1, @{T_args} node2, 'a2, 'a3, 'a4, 'a5) Z2.ZM.container
    where type @{T_args} Z3.ZM.container =
      ('p1, @{T_args} node3, 'a2, 'a3, 'a4, 'a5) Z3.ZM.container
    where type @{T_args} Z4.ZM.container =
      ('p1, @{T_args} node4, 'a2, 'a3, 'a4, 'a5) Z4.ZM.container
    where type @{T_args} Z5.ZM.container =
      ('p1, @{T_args} node5, 'a2, 'a3, 'a4, 'a5) Z5.ZM.container
    where type @{T_args} N1.node = @{T_args} node1
    where type @{T_args} N2.node = @{T_args} node2
    where type @{T_args} N3.node = @{T_args} node3
    where type @{T_args} N4.node = @{T_args} node4
    where type @{T_args} N5.node = @{T_args} node5
    where type @{T_args} N1.content = @{T_args} ncontent1
    where type @{T_args} N2.content = @{T_args} ncontent2
    where type @{T_args} N3.content = @{T_args} ncontent3
    where type @{T_args} N4.content = @{T_args} ncontent4
    where type @{T_args} N5.content = @{T_args} ncontent5
    (* where @{T_args} Zi.ZO.zcontext =
      ('p1, @{T_args} Ni.node, 'a2, 'a3, 'a4, 'a5) Zi.ZO.zcontext *)
    where type ('p1, 'a) Z1.M.t = ('p1, 'a) Z1.M.t
    where type ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
  end
  =
struct

structure Base = struct type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'n) next = 'n end
structure N1 = Node6(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'n) content = @{T_args} ncontent1)
structure N2 = Node6(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'n) content = @{T_args} ncontent2)
structure N3 = Node6(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'n) content = @{T_args} ncontent3)
structure N4 = Node6(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'n) content = @{T_args} ncontent4)
structure N5 = Node6(open Base
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'n) content = @{T_args} ncontent5)
structure A = Kleisli_Arrow(Z1.M)
structure Base = struct structure AF = SArrow_Arrow_Apply.A; structure AT = A; structure L = Z1.ZO.L;
  fun lift a = AT.arr a end
structure N1 = Lift_Node6(open Base; structure N = N1)
structure N2 = Lift_Node6(open Base; structure N = N2)
structure N3 = Lift_Node6(open Base; structure N = N3)
structure N4 = Lift_Node6(open Base; structure N = N4)
structure N5 = Lift_Node6(open Base; structure N = N5)

datatype @{T_args} next1 = Next1 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, @{T_args} next2) N2.node, 'a2, 'a3, 'a4, 'a5)
    Z2.ZM.container) Z2.ZM.Zip.M.t
and @{T_args} next2 = Next2 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, @{T_args} next3) N3.node, 'a2, 'a3, 'a4, 'a5)
    Z3.ZM.container) Z3.ZM.Zip.M.t
and @{T_args} next3 = Next3 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, @{T_args} next4) N4.node, 'a2, 'a3, 'a4, 'a5)
    Z4.ZM.container) Z4.ZM.Zip.M.t
and @{T_args} next4 = Next4 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, @{T_args} next5) N5.node, 'a2, 'a3, 'a4, 'a5)
    Z5.ZM.container) Z5.ZM.Zip.M.t
and @{T_args} next5 = Next5 of ('p1,
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, @{T_args} next1) N1.node, 'a2, 'a3, 'a4, 'a5)
    Z1.ZM.container) Z1.ZM.Zip.M.t

fun next1 x = Next1 x
fun dest_next1 (Next1 x) = x
fun next2 x = Next2 x
fun dest_next2 (Next2 x) = x
fun next3 x = Next3 x
fun dest_next3 (Next3 x) = x
fun next4 x = Next4 x
fun dest_next4 (Next4 x) = x
fun next5 x = Next5 x
fun dest_next5 (Next5 x) = x

structure Base =
struct
  type @{T_args} inst1 = 'a1
  type @{T_args} inst2 = 'a2
  type @{T_args} inst3 = 'a3
  type @{T_args} inst4 = 'a4
  type @{T_args} inst5 = 'a5
end
structure N1 = Node5_Node6(open Base
  type @{T_args} inst6 = @{T_args} next1
  structure N = N1)
structure N2 = Node5_Node6(open Base
  type @{T_args} inst6 = @{T_args} next2
  structure N = N2)
structure N3 = Node5_Node6(open Base
  type @{T_args} inst6 = @{T_args} next3
  structure N = N3)
structure N4 = Node5_Node6(open Base
  type @{T_args} inst6 = @{T_args} next4
  structure N = N4)
structure N5 = Node5_Node6(open Base
  type @{T_args} inst6 = @{T_args} next5
  structure N = N5)

structure Base =
struct
  type @{T_args} inst2 = 'a2
  type @{T_args} inst3 = 'a3
  type @{T_args} inst4 = 'a4
  type @{T_args} inst5 = 'a5
end
structure Z1 = Instantiate_Zipper5(open Base
  type @{T_args} inst1 = @{T_args} N1.node
  structure Z = Z1)
structure Z2 = Instantiate_Zipper5(open Base
  type @{T_args} inst1 = @{T_args} N2.node
  structure Z = Z2)
structure Z3 = Instantiate_Zipper5(open Base
  type @{T_args} inst1 = @{T_args} N3.node
  structure Z = Z3)
structure Z4 = Instantiate_Zipper5(open Base
  type @{T_args} inst1 = @{T_args} N4.node
  structure Z = Z4)
structure Z5 = Instantiate_Zipper5(open Base
  type @{T_args} inst1 = @{T_args} N5.node
  structure Z = Z5)

structure Base =
struct
  structure A = A
  fun ncontent x = x |> A.id ()
  fun dest_ncontent x = x |> A.id ()
end
structure N1 = Replace_Node5_Content_Next(
  open Base
  structure N = N1
  type @{T_args} ncontent = @{T_args} ncontent1
  type @{T_args} nnext = ('p1,
    @{T_args} Z2.ZM.container) Z2.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next1
  fun dest_nnext x = x |> A.arr next1
)
structure N2 = Replace_Node5_Content_Next(
  open Base
  structure N = N2
  type @{T_args} ncontent = @{T_args} ncontent2
  type @{T_args} nnext = ('p1,
    @{T_args} Z3.ZM.container) Z3.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next2
  fun dest_nnext x = x |> A.arr next2
)
structure N3 = Replace_Node5_Content_Next(
  open Base
  structure N = N3
  type @{T_args} ncontent = @{T_args} ncontent3
  type @{T_args} nnext = ('p1,
    @{T_args} Z4.ZM.container) Z4.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next3
  fun dest_nnext x = x |> A.arr next3
)
structure N4 = Replace_Node5_Content_Next(
  open Base
  structure N = N4
  type @{T_args} ncontent = @{T_args} ncontent4
  type @{T_args} nnext = ('p1,
    @{T_args} Z5.ZM.container) Z5.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next4
  fun dest_nnext x = x |> A.arr next4
)
structure N5 = Replace_Node5_Content_Next(
  open Base
  structure N = N5
  type @{T_args} ncontent = @{T_args} ncontent5
  type @{T_args} nnext = ('p1,
    @{T_args} Z1.ZM.container) Z1.ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next5
  fun dest_nnext x = x |> A.arr next5
)

type @{T_args} node1 = @{T_args} N1.node
type @{T_args} node2 = @{T_args} N2.node
type @{T_args} node3 = @{T_args} N3.node
type @{T_args} node4 = @{T_args} N4.node
type @{T_args} node5 = @{T_args} N5.node

end