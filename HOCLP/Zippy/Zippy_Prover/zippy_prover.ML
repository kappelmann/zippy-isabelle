(*  Title:      HOCLP/zippy_prover.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER =
sig
  include ZIPPY_PROVER_ARGS
  type ('p1, 'p, 'r) pzipper1 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper1
  type ('p1, 'p, 'r) pzipper2 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper2
  type ('p1, 'p, 'r) pzipper3 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper3
  type ('p1, 'p, 'r) pzipper4 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper4
  type ('p1, 'p, 'r) ppaction = ('p1, cud, 'p, 'r, unit, unit, unit, unit) paction
  type ('p1, 'p, 'r) pcopy = ('p1, cud, 'p, 'r, unit, unit, unit, unit) copy
  type ('p1, 'p, 'r) ppresults = ('p1, cud, 'p, 'r, unit, unit, unit, unit) presults

  (* misc *)
  val no_parent : ('p1, unit, 'p) cat
  val no_next : ('p1, unit, 'n) cat
  val empty_aco : unit -> ('p1, 'a, 'b, 'c) CO.acoroutine
  val with_empty_lchildren : 'n -> 'n * 'n ZACT.rose

  (* lenses *)
  val content1 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N1.content) L.slens
  val content2 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N2.content) L.slens
  val content3 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N3.content) L.slens
  val content4 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N4.content) L.slens
  val next1 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z1.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N1.next) L.slens
  val next2 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N2.next) L.slens
  val next3 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N3.next) L.slens
  val next4 : unit ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) AZN.N4.next) L.slens

  (* nodes *)
  val mk_gcs_node : ('p1, 'a1, ('p1, ('a1, unit) GCSD.gclusters_data, 'a2, 'a3, 'a4) node1) cat
  val is_gcs_finished : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1, bool) cat

  val cons_lactions_sibling :
    ('p1, 'a1, 'a2, 'a3, 'a4) node3 * ('p1, 'a1, 'a2, 'a3, 'a4) node3 ZACT.rose ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper) hom_move
  val cons_laction_sibling :
    ('p1, 'a1, 'a2, 'a3, 'a4) node4 * ('p1, 'a1, 'a2, 'a3, 'a4) node4 ZACT.rose ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper) hom_move
  val cons_lactions_child :
    ('p1, 'a1, 'a2, 'a3, 'a4) node3 * ('p1, 'a1, 'a2, 'a3, 'a4) node3 ZACT.rose ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper) hom_move
  val cons_laction_child :
    ('p1, 'a1, 'a2, 'a3, 'a4) node4 * ('p1, 'a1, 'a2, 'a3, 'a4) node4 ZACT.rose ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper) hom_move

  (*TODO: remove*)
  val finish_gcluster_list' : Proof.context ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2 list, GCS.state list Seq.seq) cat

  val get_gcluster_list_thmsq' : Proof.context ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1, GCS.state list Seq.seq) cat

  val finish_gcluster' : Proof.context ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2, GCS.state Seq.seq) cat

  val finish_gclusters' : Proof.context ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1, GCS.state Seq.seq) cat

  val mk_gc_nodes : ('p1, 'gc list,
    ('p1, 'a1, ('gc, unit) GCD.gcluster_data, 'a3, 'a4) node2 list) cat
  val set_gc_list : GC.gcluster list -> ('p1, ('p1, 'p, 'r) pzipper1) hom_move

  val mk_actions_node : ('p1, 'cd, ('p1, 'a1, 'a2, ('cd, unit) CD.copy_data, 'a4) node3) cat
  val cons_move_actions :
    ('p1, 'a1, 'a2, 'a3, 'a4) node3 * ('p1, 'a1, 'a2, 'a3, 'a4) node3 ZACT.rose ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z2.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper) cat

  val mk_action_node : 'pa -> 'r -> 'f -> ('p1, 'an, ('p1, 'a1, 'a2, 'a3,
    ('pa, ('r, ('f, ('an, unit) AND.action_num_data) FD.focus_data) RD.result_data) PAD.paction_data)
    node4) cat
  val cons_move_action :
    ('p1, 'a1, 'a2, 'a3, 'a4) node4 * ('p1, 'a1, 'a2, 'a3, 'a4) node4 ZACT.rose ->
    ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) Z3.zipper, ('p1, 'a1, 'a2, 'a3, 'a4) Z4.zipper) cat

  val set_gcs : GCS.gclusters -> ('p1, ('p1, 'p, 'r) pzipper4, ('p1, 'p, 'r) pzipper1) cat

  val init_state : ('p1, GCS.state, cud * ('p1, 'p, 'r) pzipper1) cat

  (* copy *)
  (** run copies **)
  val get_run_copy : 'cud -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move

  val copy_parent_actions :
    (*foldM*)
    ((('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
        ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
      'z3s -> ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    'cud -> 'z3s -> ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move

  (** make copy **)
  val copy_cpfocus : (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 -> 'f ->
      ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2, 'z1) cat) ->
    (GCS.cluster_pos * 'f) -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1, 'z1) cat

  val copy_cpfocuss : (('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 -> 'f -> ('p1,
      ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2,
      ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) cat) ->
    (GCS.cluster_pos * 'f) list -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move

  val copy_update_focus :
    (('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 -> F.focus -> ('p1,
      ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2,
      ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) cat) ->
    F.focus -> ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy

  (* presults *)
  val presults_from_sq : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 * 'r Seq.seq,
      'p * 'r Seq.seq) CO.coroutine ->
    'r Seq.seq -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults

  val presults_from_tac_state : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 * 'r Seq.seq,
      'p * 'r Seq.seq) CO.coroutine ->
    (GCS.state -> 'r Seq.seq) -> GCS.state -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults

  val presults_from_tac : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4 * 'r Seq.seq,
      'p * 'r Seq.seq) CO.coroutine ->
    (GCS.state -> 'r Seq.seq) -> ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper2,
      ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults) cat

  (* actions *)
  val no_paction : unit -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction
  val disable_paction : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move

  val get_run_paction : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4,
    'p * ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) action) move
  val run_action : 'p * ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) action ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move

  val update_result_update_data : TR.result_update_data ->
    ('p1, ('p1, 'p, 'r) pzipper4, ('p1, 'p, 'r) pzipper1) cat

  (** action from presult **)
  val update_presults_tail_aco :
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4, 'p, 'r) CO.acoroutine ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move

  val update_result_update_data_presults_tail_aco : TR.result_update_data *
      ('p1, ('p1, 'p, 'r) pzipper4, 'p, 'r) CO.acoroutine ->
    ('p1, ('p1, 'p, 'r) pzipper4) hom_move

  val get_presults : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4,
    ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) presults) cat
  val get_presults_aco : ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4,
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4, 'p, 'r) CO.acoroutine) cat

  val gen_presults_paction :
    ('p -> 'r * ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4, 'p, 'r) CO.acoroutine ->
      ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper4) hom_move) ->
    ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) paction

  val presults_paction : unit -> ('p1, 'p, TR.result_update_data) ppaction

  val gen_add_presults_action_copy :
    (F.focus -> ('p1, ('p1, 'p, 'r) pzipper2, ('p1, 'p, 'r) ppresults) cat) ->
    ('p -> 'r * ('p1, ('p1, 'p, 'r) pzipper4, 'p, 'r) CO.acoroutine ->
      ('p1, ('p1, 'p, 'r) pzipper4) hom_move) ->
    ('p1, 'p, 'r) pcopy -> F.focus -> ('p1, ('p1, 'p, 'r) pzipper2, ('p1, 'p, 'r) pzipper4) cat

  val gen_add_presults_action :
    (F.focus -> ('p1, ('p1, 'p, 'r) pzipper2, ('p1, 'p, 'r) ppresults) cat) ->
    ('p -> 'r * ('p1, ('p1, 'p, 'r) pzipper4, 'p, 'r) CO.acoroutine ->
      ('p1, ('p1, 'p, 'r) pzipper4) hom_move) ->
    F.focus -> ('p1, ('p1, 'p, 'r) pzipper2, ('p1, 'p, 'r) pzipper4) cat

  val add_presults_action :
    (F.focus -> ('p1, ('p1, 'p, TR.result_update_data) pzipper2,
      ('p1, 'p, TR.result_update_data) ppresults) cat) ->
    F.focus -> ('p1, ('p1, 'p, TR.result_update_data) pzipper2,
      ('p1, 'p, TR.result_update_data) pzipper4) cat

  (* tactics *)
  structure T : ZIPPY_TACTIC
  sharing type T.GC.GCS.gcpos = TR.GC.GCS.gcpos
  sharing type T.GC.GCS.gclusters = TR.GC.GCS.gclusters
  sharing type T.GC.gcluster= TR.GC.gcluster
  sharing type T.GPU.F.focus= TR.GPU.F.focus

end

functor Zippy_Prover(A : ZIPPY_PROVER_ARGS) : ZIPPY_PROVER =
struct

open A

type ('p1, 'p, 'r) pzipper1 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper1
type ('p1, 'p, 'r) pzipper2 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper2
type ('p1, 'p, 'r) pzipper3 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper3
type ('p1, 'p, 'r) pzipper4 = ('p1, cud, 'p, 'r, unit, unit, unit, unit) zipper4
type ('p1, 'p, 'r) ppaction = ('p1, cud, 'p, 'r, unit, unit, unit, unit) paction
type ('p1, 'p, 'r) pcopy = ('p1, cud, 'p, 'r, unit, unit, unit, unit) copy
type ('p1, 'p, 'r) ppresults = ('p1, cud, 'p, 'r, unit, unit, unit, unit) presults

local
  structure SC = Semi_Category(Z1); structure M = Monad(M); structure A = Kleisli_Arrow(M)
  structure C = Category(A); structure AA = Kleisli_Arrow_Apply(M)
  structure AE = Kleisli_Arrow_Exception(ZGC.LI.M)
  structure LT = List_Traversable_Trans(Identity_Traversable(M))
  structure LF = Foldable_Monad(structure F = List_Foldable_Trans(Identity_Foldable); structure M = M)
  open SC M A
in

structure CO = Coroutine_Util(structure AE = AE; structure CO = CO)
structure AU = Zippy_Action_Util(structure AE = AE; structure CO = CO)

(* misc *)
fun seq_snoc sq x = Seq.append sq (Seq.single x)

structure LK = Lens_Kleisli_Exception(structure AE = AE; structure L = L)
fun set_safe l = LK.set_safe l
fun map_monad l = LK.lens_monad l |> L.modify

fun no_parent _ = AE.throw ()
fun no_next _ = AE.throw ()
fun empty_aco _ = CO.throw ()

fun with_empty_lchildren x = (x, ZACT.rose [])

fun set_next next = next |> L.set |> curry
fun set_no_next next = set_next next (no_next ())

(* lenses *)
fun content1 _ = Z1.ZO.content () |> L.comp (AZN.N1.content ())
fun content2 _ = Z2.ZO.content () |> L.comp (AZN.N2.content ())
fun content3 _ = Z3.ZO.content () |> L.comp (AZN.N3.content ())
fun content4 _ = Z4.ZO.content () |> L.comp (AZN.N4.content ())
fun next1 _ = Z1.ZO.content () |> L.comp (AZN.N1.next ())
fun next2 _ = Z2.ZO.content () |> L.comp (AZN.N2.next ())
fun next3 _ = Z3.ZO.content () |> L.comp (AZN.N3.next ())
fun next4 _ = Z4.ZO.content () |> L.comp (AZN.N4.next ())

(* nodes *)
fun mk_gcs_node x = x |>
  ((rpair () #> GCSD.gclusters_data)
  >>> (rpair (no_next ()) #> AZN.N1.node))

fun get_gcsd x = x |> (content1 () |> L.get)
fun get_gcs_state x = x |> (get_gcsd >>> GCSD.get_gclusters >>> arr GCS.get_state)
fun is_gcs_finished x = x |> gen_is_gcs_finished get_gcsd

fun gen_cons_lnode cons_lzcontext map_lzcontext = first (arr cons_lzcontext) >>> map_lzcontext
fun cons_sibling_lzcontext x = arr (ZACT.cons_sibling_zcontext x)
fun cons_lsibling map_lzcontext = curry (gen_cons_lnode cons_sibling_lzcontext map_lzcontext)
fun cons_child_lzcontext x = arr (ZACT.cons_child_zcontext x)
fun cons_lchild map_lzcontext = curry (gen_cons_lnode cons_child_lzcontext map_lzcontext)

fun cons_lactions_sibling x = x |>
  cons_lsibling (Z3.ZO.zcontext () |> L.comp (AZN.lzcontext3 ()) |> L.modify)
fun cons_laction_sibling x = x |>
  cons_lsibling (Z4.ZO.zcontext () |> L.comp (AZN.lzcontext4 ()) |> L.modify)
fun cons_lactions_child x = x |>
  cons_lchild (Z3.ZO.zcontext () |> L.comp (AZN.lzcontext3 ()) |> L.modify)
fun cons_laction_child x = x |>
  cons_lchild (Z4.ZO.zcontext () |> L.comp (AZN.lzcontext4 ()) |> L.modify)

(*FIXME: enums*)
fun list_container_zippers1 x = x |>
  (gen_list_container_zippers Z1.ZM.Unzip.move Z1.ZM.Zip.move Z1.ZM.Down.move)
fun list_container_zippers2 x = x |>
  (gen_list_container_zippers Z2.ZM.Unzip.move Z2.ZM.Zip.move Z2.ZM.Down.move)
fun list_container_zippers3 x = x |>
  (gen_list_container_zippers Z3.ZM.Unzip.move Z3.ZM.Zip.move Z3.ZM.Down.move)
fun list_container_zippers4 x = x |>
  (gen_list_container_zippers Z4.ZM.Unzip.move Z4.ZM.Zip.move Z4.ZM.Down.move)

fun gen_cons_move_node next down n =
  AE.catch' ((next |> map_monad |> curry) (arr (ZACT.cons n))) (set_next next (pure (ZACT.rose [n])))
  >>> down

fun gen_finish_gclusters get_gcluster_list_thmsq get_gcsd ctxt x = x |>
  (AE.catch' get_gcluster_list_thmsq (K Seq.empty) &&& (get_gcsd >>> GCSD.get_gclusters)
  >>> arr (fn (gcluster_thmssq, gcs) =>
    Seq.maps (fn gcluster_thms => GCS.finish_cluster_thms ctxt gcluster_thms gcs) gcluster_thmssq)
  >>> (fn gclusters_thmsq => get_gcs_state x
  >>= arr (seq_snoc gclusters_thmsq)))

fun gen_get_gcluster_list_thmsq finish_gcluster_list =
  Down1.move
  >>> list_container_zippers2
  >>> finish_gcluster_list
  >>> arr (Seq.map (List.map Zippy_Thm_State.get_thm))

local structure LTSM =
  Traversable(List_Traversable_Trans(Identity_Traversable(Seq_Monad_Trans(M))))
in
fun gen_finish_gcluster_list finish_gcluster = LTSM.traverse finish_gcluster
end

fun gcd _ = Z2.ZO.content () |> L.comp (AZN.N2.content ())
fun gcluster _ = gcd () |> L.comp (GCD.gcluster ())
fun get_gcluster_state x = x |> (gcluster () |> L.get >>> arr GC.get_state)

fun gen_finish_gcluster list_gcluster_children fold_add finish_gclusters x = x |>
  (AE.catch' list_gcluster_children (K [])
  >>> (fn gcs => fold_add finish_gclusters gcs Seq.empty)
  >>> (fn gcs_thmssq => get_gcluster_state x
  >>= arr (seq_snoc gcs_thmssq)))

fun finish_gclusters list_gcluster_children fold_add ctxt x = x |>
  gen_finish_gclusters (get_gcluster_list_thmsq list_gcluster_children fold_add ctxt) get_gcsd ctxt
and get_gcluster_list_thmsq list_gcluster_children fold_add ctxt x = x |>
  gen_get_gcluster_list_thmsq (finish_gcluster_list list_gcluster_children fold_add ctxt)
and finish_gcluster_list list_gcluster_children fold_add ctxt x = x |>
  gen_finish_gcluster_list (finish_gcluster list_gcluster_children fold_add ctxt)
and finish_gcluster list_gcluster_children fold_add ctxt x = x |>
  gen_finish_gcluster list_gcluster_children fold_add
    (finish_gclusters list_gcluster_children fold_add ctxt)

fun list_zipper4_gcluster_children x = x |> (Down4.move >>> list_container_zippers1)
fun list_zipper3_gcluster_children x = x |>
  (Down3.move
  >>> list_container_zippers4
  >>> LT.traverse (AE.catch' list_zipper4_gcluster_children (K []))
  >>> arr List.concat)
fun list_zipper2_gcluster_children x = x |>
  (Down2.move
  >>> list_container_zippers3
  >>> LT.traverse (AE.catch' list_zipper3_gcluster_children (K []))
  >>> arr List.concat)

fun gen_fold_add_finish_gclusters fold f = fold (fn x => fn acc => f x >>= arr (Seq.append acc))
fun foldl_add_finish_gclusters f = gen_fold_add_finish_gclusters LF.foldlM f
fun foldr_add_finish_gclusters f = gen_fold_add_finish_gclusters LF.foldrM f

fun get_gcluster_list_thmsq' x = x
  |> get_gcluster_list_thmsq list_zipper2_gcluster_children foldr_add_finish_gclusters

fun finish_gcluster_list' x = x
  |> finish_gcluster_list list_zipper2_gcluster_children foldl_add_finish_gclusters

fun finish_gcluster' x = x
  |> finish_gcluster list_zipper2_gcluster_children foldl_add_finish_gclusters

fun finish_gclusters' x = x
  |> finish_gclusters list_zipper2_gcluster_children foldl_add_finish_gclusters

fun mk_gc_node x = x |>
  ((rpair () #> GCD.gcluster_data)
  >>> (rpair (no_next ()) #> AZN.N2.node))

fun mk_gc_nodes gcs = LT.traverse mk_gc_node gcs

fun set_gc_list gcs x = mk_gc_nodes gcs
  >>= (fn ns => (next1 () |> set_safe) (pure ns, x))

fun mk_actions_node x = x |>
  ((rpair () #> CD.copy_data)
  >>> (rpair (no_next ()) #> AZN.N3.node))

fun cons_move_actions x = x |>
  gen_cons_move_node (Z2.ZO.content () |> L.comp (AZN.N2.next ())) Down2.move

fun mk_action_node paction presults focus =
  (rpair () #> AND.action_num_data)
  >>> (pair focus #> FD.focus_data)
  >>> (pair presults #> RD.result_data)
  >>> (pair paction #> PAD.paction_data)
  >>> (rpair (no_next ()) #> AZN.N4.node)

fun cons_move_action x = x |>
  gen_cons_move_node (Z3.ZO.content () |> L.comp (AZN.N3.next ())) Down3.move

fun set_gcs gcs x = mk_gcs_node gcs
  >>= (fn n => (next4 () |> set_safe) (pure n, x)
  >>= Down4.move)

fun init_state state = state |>
  (arr (rpair TR.GPU.id #> TR.RUD.result_update_data #> TR.init_result_update_data)
  >>> second (
    arr swap
    >>> second (
      mk_gcs_node
      >>> (rpair (no_parent ()) #> Z1.ZM.Zip.move))
    >>> AA.uncurry set_gc_list))

(* copy *)
(** run copies **)
fun get_copy_data x = x |> (Z3.ZO.get_content >>> AZN.N3.get_content)
fun get_run_copy x = x |> gen_get_run_copy get_copy_data

fun copy_parent_actions foldM = gen_copy_parent_actions foldM get_copy_data

(** make copy **)
fun move_cpos cpos = Down1.move >>> C.repeatn cpos Z2.ZM.Down.move

fun copy_cpfocus init_copy = gen_copy_cpfocus move_cpos init_copy

fun copy_cpfocuss init_copy = gen_copy_cpfocuss LF.foldlM (copy_cpfocus init_copy)
fun copy_update_focus init_copy = gen_copy_update_focus (copy_cpfocuss init_copy)

(* presults *)
fun presults_from_sq mk_prio_sq_c = AU.aco_from_sq (empty_aco ()) mk_prio_sq_c #> mk_presults
fun presults_from_tac_state mk_prio_sq_c tac state = tac state |> presults_from_sq mk_prio_sq_c

fun get_gc_state x = x |>
  (Z2.ZO.get_content >>> AZN.N2.get_content >>> GCD.get_gcluster >>> arr GC.get_state)

fun presults_from_tac mk_prio_sq_c tac =
  get_gc_state >>> arr (presults_from_tac_state mk_prio_sq_c tac)

(* actions *)
fun no_paction _ = AE.throw' () |> mk_paction

fun node_paction _ = AZN.N4.content () |> L.comp (PAD.paction ())
fun paction _ = Z4.ZO.content () |> L.comp (node_paction ())

fun get_run_paction x = (paction () |> L.get) x >>= (fn paction => dest_paction paction x)
fun run_action (p, action) = action p

fun disable_paction x = x |> (paction () |> L.set |> curry) (no_paction ())

(*TODO: generalise enumeration of zipper; double check foldlM or foldrM*)
fun update_result_update_data x = x |>
  gen_update_result_update_data set_gcs set_gc_list LF.foldlM
    (Up1.move >>> Up4.move >>> list_container_zippers3) get_copy_data

(** action from presult **)
fun node_presults _ = AZN.N4.content () |> L.comp (PAD.more ()) |> L.comp (RD.result ())

fun node_action_num _ = AZN.N4.content () |> L.comp (PAD.more ()) |> L.comp (RD.more ())
  |> L.comp (FD.more ()) |> L.comp (AND.action_num ())

fun inc_node_action_num x = x |> (node_action_num () |> L.modify |> curry) (arr next_action_num)

(*add a new sibling containing the tail actions*)
fun update_presults_tail_aco aco =
  Z4.ZO.get_content &&& id ()
  >>> first ((node_presults () |> L.set |> curry) (mk_presults aco)
    >>> set_no_next (AZN.N4.next ())
    >>> inc_node_action_num
    >>> arr with_empty_lchildren)
  >>> uncurry cons_laction_child

fun update_result_update_data_presults_tail_aco x = x |>
  AU.update_result_tail_aco (fn x => update_result_update_data x >>> Up1.move)
    (fn aco => update_presults_tail_aco aco >>> disable_paction)

fun get_presults x = x |>
  (Z4.ZO.get_content >>> AZN.N4.get_content >>> PAD.get_more >>> RD.get_result)
fun get_presults_aco x = x |> (get_presults >>> arr dest_presults)

fun gen_presults_paction update_result_tail_aco =
  AU.paction_from_aco disable_paction update_result_tail_aco get_presults_aco |> mk_paction

fun presults_paction _ =
  gen_presults_paction (Library.K update_result_update_data_presults_tail_aco)

fun mk_presults_action_node update_result_tail_aco =
  mk_action_node (gen_presults_paction update_result_tail_aco)

fun gen_add_presults_action_copy mk_presults update_result_tail_aco copy focus x = x |>
  (mk_presults focus
  >>> (fn presults => mk_actions_node copy
  >>= (fn n => cons_move_actions (with_empty_lchildren n) x)
  >>= (fn x => mk_presults_action_node update_result_tail_aco presults focus init_action_num
  >>= (fn n => cons_move_action (with_empty_lchildren n) x))))

fun gen_add_presults_action mk_presults update_result_tail_aco focus =
  let
    fun init_copy _ focus = AE.try (gen_add_presults_action mk_presults update_result_tail_aco focus
      >>> Up4.move >>> Up3.move)
      >>> Up2.move
    val copy = copy_update_focus init_copy focus
  in gen_add_presults_action_copy mk_presults update_result_tail_aco copy focus end

fun add_presults_action mk_presults =
  gen_add_presults_action mk_presults (Library.K update_result_update_data_presults_tail_aco)

(** tactics **)
structure T = Zippy_Tactic(TR)

end

end
