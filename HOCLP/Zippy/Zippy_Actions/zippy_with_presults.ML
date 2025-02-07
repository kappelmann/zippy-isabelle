(*  Title:      HOCLP/zippy_with_presults.ML
    Author:     Kevin Kappelmann

Zippy with prioritised action results.
*)
signature ZIPPY_WITH_PRESULTS =
sig
  type result
  (** action number **)
  type action_num = int
  val init_action_num : int
  val next_action_num : int -> int

  structure PRD : KLEISLI_ZIPPY_PRESULTS_DATA
  structure AND : ZIPPY_ACTION_NUM_DATA
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) PRD.L.C.cat
  sharing type AND.L.lens = PRD.L.lens
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more

  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults

  include ZIPPY_WITH_PACTION
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more = (('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults,
    (action_num, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more) AND.action_num_data)
    PRD.presults_data
  where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more =
    (action_num, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more) AND.action_num_data
  where type ('p1, 'a) M.t = ('p1, 'a) PRD.K.M.t
  where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) PRD.L.lens

  structure CO : COROUTINE
  where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) cat

  val mk_presults : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, prio, result) CO.acoroutine ->
    ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults
  val dest_presults : ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) Z4.zipper, prio, result) CO.acoroutine
end

functor Zippy_With_PResults(
    type result
    structure PRD : KLEISLI_ZIPPY_PRESULTS_DATA
    structure AND : ZIPPY_ACTION_NUM_DATA
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) PRD.L.C.cat
    sharing type AND.L.lens = PRD.L.lens
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more

    structure Z : ZIPPY_WITH_PACTION
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pad_more = 'a4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pd_more = 'a5
    where type ('p1, 'a) M.t = ('p1, 'a) PRD.K.M.t
    where type ('p1, 't, 's, 'i, 'o) L.lens = ('p1, 't, 's, 'i, 'o) PRD.L.lens

    structure CO : COROUTINE
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) Z.cat
  ) : ZIPPY_WITH_PRESULTS =
struct

type result = result
(** action number **)
type action_num = int
val init_action_num = 0
val next_action_num = General_Util.succ

structure PRD = PRD
structure AND = AND
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more
type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more
structure CO = CO

open Z
datatype ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'prdm) presults = PResults of
  ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'prdm) zipper4, prio, result) CO.acoroutine
withtype ('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'prdm) zipper4 = ('p1, 'a1, 'a2, 'a3,
  (('p1, 'a1, 'a2, 'a3, 'a4, 'a5, 'prdm) presults, 'prdm) PRD.presults_data, 'a5) Z4.zipper

fun mk_presults presults = PResults presults
fun dest_presults (PResults presults) = presults

type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults = ('p1, 'a1, 'a2, 'a3, 'a4,
  (action_num, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more) AND.action_num_data,
  (action_num, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more) AND.action_num_data) presults

structure Z = Instantiate_Zippy_With_PAction(
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1 = 'a1
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2 = 'a2
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3 = 'a3
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4 = (('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults,
    (action_num, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more) AND.action_num_data) PRD.presults_data
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5 =
    (action_num, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more) AND.action_num_data
  structure Z = Z
)
open Z

end

functor Instantiate_Zippy_With_PResults(
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4
    type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5
    structure Z : ZIPPY_WITH_PRESULTS
  ) :
    ZIPPY_WITH_PRESULTS
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z1.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z1.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z2.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z2.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z3.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z3.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z4.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z4.zipper
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZM.container = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZM.container
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZO.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZO.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.ZO.zcontext = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.ZO.zcontext
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.Z5.zipper = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.Z5.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.N1.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.N1.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) A.N2.content = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.A.N2.content
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext1
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext2
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext3
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) zcontext5 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.zcontext5
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper1 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper1
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper2 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper2
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper3 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper3
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper4 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper4
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) pzipper5 = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.pzipper5
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) cd_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.cd_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) action_and_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.action_and_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) aaction_and_more = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.aaction_and_more
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) paction = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.paction
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) copy = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.copy
    where type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) presults = ('p1, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3,
      ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4, ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5) Z.presults =
struct
open Z
structure Base =
struct
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst1
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst2
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst3
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst4
  type ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5 = ('p1, 'a1, 'a2, 'a3, 'a4, 'a5) inst5
end
structure Z = Instantiate_Zippy_With_PAction(open Base; structure Z = Z)
open Z
end
