(*  Title:      HOCLP/hoclp.ML
    Author:     Kevin Kappelmann
*)
signature HOCLP =
sig
end

structure HOCLP
  (* : HOCLP  *)
  =
struct

structure CMA = Content_Mk_Action(structure A = SIn.LA.A; structure L = SIn.LA.LE)
structure CO = Coroutine_Util(
  structure CO = Coroutine(SIn.LA.A)
  structure AE = SIn.LA.AE
)
structure MA : MK_ACTION =
struct
  structure C = SIn.LA.A
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'r) data_functor =
    ('p1, 'a1, 'a2, 'a3, ('a4, 'r) CMA.cma) AZ.Z4.zipper
  type ('p1, 'p, 'a1, 'a2, 'a3, 'a4, 'r) mk_action_functor = ('p1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'r) data_functor,
      'p * ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'r) data_functor,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'r) data_functor) C.cat
    ) C.cat
  datatype ('p1, 'p, 'a1, 'a2, 'a3, 'a4) mk_action = Mk_Action of
    ('p1, 'p, 'a1, 'a2, 'a3, 'a4, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) mk_action) mk_action_functor
  type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data =
    ('p1, 'a1, 'a2, 'a3, 'a4, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) mk_action) data_functor
  type ('p1, 'p, 'a1, 'a2, 'a3, 'a4) to =
    'p * ('p1, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data, ('p1, 'p, 'a1, 'a2, 'a3, 'a4) data) C.cat
  fun mk_action mka = Mk_Action mka
  fun run (Mk_Action mka) = mka
end
structure MAU = Mk_Action_Util(
  open SIn.LA
  structure MA = MA
  structure CO = CO
)

structure E1 = DFS_Postorder_Enumerable_Zipper4(structure AE = SIn.LA.AE; structure Z = AZ.Z1.ZM)
structure E2 = DFS_Postorder_Enumerable_Zipper4(structure AE = SIn.LA.AE; structure Z = AZ.Z2.ZM)
structure E3 = DFS_Postorder_Enumerable_Zipper4(structure AE = SIn.LA.AE; structure Z = AZ.Z3.ZM)
structure E4 = DFS_Postorder_Enumerable_Zipper4(structure AE = SIn.LA.AE; structure Z = AZ.Z4.ZM)
local structure E1' = E1; structure E2' = E2; structure E3' = E3; structure E4' = E4
in
structure Base = struct structure AE = SIn.LA.AE; structure L = SIn.LA.L end
structure T1 = Test(open Base; structure AZ = AZ;
  structure E1 = E1; structure E2 = E2; structure E3 = E3; structure E4 = E4)
structure T2 = Test(open Base; structure AZ = Rotate_Alternating_Zippers4(AZ);
  structure E1 = E2'; structure E2 = E3'; structure E3 = E4; structure E4 = E1')
structure T3 = Test(open Base; structure AZ = Rotate_Alternating_Zippers4(Rotate_Alternating_Zippers4(AZ));
  structure E1 = E3'; structure E2 = E4'; structure E3 = E1'; structure E4 = E2')
structure T4 = Test(open Base; structure AZ = Rotate_Alternating_Zippers4(Rotate_Alternating_Zippers4(Rotate_Alternating_Zippers4(AZ)));
  structure E1 = E4'; structure E2 = E1'; structure E3 = E2'; structure E4 = E3')
end

local type ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4, 'r) ac_functor =
  ('p1, 'p, 'x, 'a1, 'a2, 'r, 'a4) MAU.pd_ac
in
datatype ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac = Ac of ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac
withtype ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac =
  ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac) ac_functor

type ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4 =
  ('p1, 'p, 'a1, 'a2, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac, 'a4) MA.data
type ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) node4 = ('p1, 'a1, 'a2,
    ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac,
    ('a4, ('p1, 'p, 'a1, 'a2, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac, 'a4) MA.mk_action) CMA.cma
  ) AZ.N4.node
type ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) mk_action =
  ('p1, 'p, 'a1, 'a2, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) ac, 'a4) MA.mk_action
end

fun ac x = Ac x
fun dest_ac (Ac ac) = ac


local structure LE = SIn.LA.LE; structure MU = Move_Util(open SIn.LA) open MU MU.SC MU.A in
fun mk_prio_sq_c prio =
  arr (fn (_, sq) => ((prio, sq), mk_prio_sq_c (Prio.halve prio)))
  |> CO.coroutine
fun ac_empty_sq _ = CO.throw ()
fun ac_from_sq get_sq = MAU.ac_from_sq (ac_empty_sq ()) (mk_prio_sq_c Prio.HIGH) get_sq
fun mk_child content
:
  ('p1, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac * ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4,
  ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) node4) cat
  =
  let
    val get = AZ.Z4.ZO.content () |> LE.comp (AZ.N4.content ()) |> LE.comp (CMA.mk_action ())
      |> LE.get
    val mk_node_no_child = arr (pair content)
      >>> CMA.content_mk_action
      >>> arr (rpair AE.throw)
      >>> AZ.N4.node
  in arr snd >>> get >>> mk_node_no_child end
fun append_child _ =
  let val map = AZ.Z4.ZO.zcontext () |> LE.comp (AZ.lzcontext4 ()) |> LE.modify
  in
    arr (fn (ch : ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) node4,
      zipper : ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4) =>
      (ch, zipper))
    >>> first (arr (Data_Zipper.append_zcontext #> arr))
    >>> map
  end
  |> Lazy_Cat_Util.unlift
fun update_tail_ac _
  (* : ('p1, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac *)
    (* * ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4) AZ.Z4.cat *)
(* = fn _ =>  *)
=
  let
    val map = AZ.Z4.ZO.zcontext () |> LE.comp (AZ.parent4 ()) |> LE.modify
    val set = AZ.PZO4.content () |> LE.set
    fun map_parent4 ac = AA.app' () >>> arr (pair ac) >>> set >>> arr K
  in first (arr (ac #> map_parent4)) >>> map end
  |> Lazy_Cat_Util.unlift
fun update_ac content
  : ('p1, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac * ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4,
    ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4) AZ.Z4.cat
    =
  MAU.update_ac (mk_child content) append_child update_tail_ac
fun update_ac_disable_mk_action content
  : ('p1, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) pz_ac * ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4,
    ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4) AZ.Z4.cat
  =
  let
    val exn = ()
    val set_mk_action :
      (('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) mk_action ->
      ('p1, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4, ('p1, 'p, 'x, 'a1, 'a2, 'a3, 'a4) zipper4) AZ.Z4.cat)
    = AZ.Z4.ZO.content () |> LE.comp (AZ.N4.content ()) |> LE.comp (CMA.mk_action ())
      |> LE.set |> curry
  in MAU.update_ac_disable_mk_action exn set_mk_action (update_ac content) end
fun update_pulled _
  =
  let
    val init_nodes = AZ.N1.node >>> arr (fn node => SIn.LGList.cons node SIn.LGList.empty)
    val set = AZ.Z4.ZO.content () |> LE.comp (AZ.N4.next ()) |> LE.set
  in first (arr (rpair AE.throw) >>> init_nodes >>> arr K) >>> set end
  |> Lazy_Cat_Util.unlift
fun update_data content _
  : ('p1, ('a1 * ('p1, 'p, 'a1, 'a1, 'a2, 'a3, 'a4) pz_ac) * ('p1, 'p, 'a1, 'a1, 'a2, 'a3, 'a4) zipper4,
    ('p1, 'p, 'a1, 'a1, 'a2, 'a3, 'a4) zipper4) AZ.Z4.cat
  = MAU.update_data update_pulled (update_ac_disable_mk_action content)
fun get_ac _
(* : ('p1, ('p1, 'p, 'a1, 'a1, 'a2, 'a3, 'a4) zipper4, ('p1, 'p, 'a1, 'a1, 'a2, 'a3, 'a4) pz_ac) AZ.Z4.cat *)
(* = fn _ =>  *)
=
  let val get = AZ.Z3.ZO.content () |> LE.comp (AZ.N3.content ()) |> LE.get
  in AZ.Up4.move >>> get >>> arr dest_ac end
  |> Lazy_Cat_Util.unlift
fun mk_action content : ('p1, 'p, 'a1, 'a1, 'a2, 'a3, 'a4) mk_action =
  MAU.mk_action_from_ac (update_data content) get_ac
end

end