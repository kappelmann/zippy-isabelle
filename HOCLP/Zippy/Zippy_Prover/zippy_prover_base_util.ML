(*  Title:      HOCLP/zippy_prover_base_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_PROVER_BASE_UTIL =
sig
  include ZIPPY_PROVER_BASE
  structure TR : ZIPPY_TACTIC_RESULT
  sharing type TR.GPU.GCS.gcpos = GCS.gcpos
  sharing type TR.GPU.GCS.gclusters = GCS.gclusters
  sharing type TR.GC.gcluster = GC.gcluster
  sharing type TR.GPU.F.focus = F.focus

  (* misc *)
  val gen_is_gcs_finished : ('p1, 'a, (GCS.gclusters, 'b) GCSD.gclusters_data) cat ->
    ('p1, 'a, bool) cat

  (* copy *)
  (** make copy **)
  val gen_copy_cpfocus :
    (*move to cluster position*)
    ('cpos -> ('p1, 'z1, 'z2) cat) ->
    (*initialise the copy*)
    ('z3 -> 'f -> ('p1, 'z2, 'z4) cat) ->
    ('cpos * 'f) -> 'z3 -> ('p1, 'z1, 'z4) cat

  val gen_copy_cpfocuss :
    (*foldM*)
    (('cpf -> ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
      'cpfs -> ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    ('cpf -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
      ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    'cpfs -> ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
    ('p1, ('p1, 'cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move

  val gen_copy_update_focus :
    ('cpfs -> ('p1, 'f -> 'cpfs, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
      ('p1, ('p1, 'f -> 'cpfs, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    'f -> ('p1, 'f -> 'cpfs, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy

  (* actions *)
  type cud = F.focus -> (GCS.cluster_pos * F.focus) list

  val init_result_update_data : (GCS.gclusters -> ('p1, 'z4, 'z1) cat) ->
    (GC.gcluster list -> ('p1, 'z1, 'z2) cat) -> TR.result_update_data -> ('p1, 'z4, cud * 'z2) cat

  val gen_update_result_update_data : (GCS.gclusters -> ('p1, 'z4, 'z1) cat) ->
    (GC.gcluster list -> ('p1, 'z1, ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) cat) ->
    (*foldM*)
    ((('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
        ('p1, ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
      'z3s -> ('p1, ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    (* get parent zippers3 *)
    ('p1, ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1, 'z3s) cat ->
    ('p1, ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3,
      (('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy, 'd) CD.copy_data) cat ->
    TR.result_update_data -> ('p1, 'z4, ('p1, cud, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) cat

  (** action priorities **)
  val Kupdate_prio_co : ('p -> 'p) -> 'p -> ('p1, 'x * 'sq, 'p * 'sq) CO.coroutine

end

functor Zippy_Prover_Base_Util(
    structure Z : ZIPPY_PROVER_BASE
    structure AU : ZIPPY_ACTION_UTIL
    sharing type AU.AE.K.M.t = Z.K.M.t
    structure TR : ZIPPY_TACTIC_RESULT
    sharing type TR.GC.GCS.gcpos = Z.GCS.gcpos
    sharing type TR.GC.GCS.gclusters = Z.GCS.gclusters
    sharing type TR.GC.gcluster = Z.GC.gcluster
    sharing type TR.GPU.F.focus = Z.F.focus
  ) : ZIPPY_PROVER_BASE_UTIL =
struct

open Z

structure TR = TR

local structure SC = Semi_Category(Z); structure M = Monad(K.M) structure AE = AU.AE
  structure AA = Kleisli_Arrow_Arrow_Apply(M)
  structure CO = Coroutine_Util_Apply(
    structure A = AA; structure CO = Coroutine_Util(structure AE = AE; structure CO = CO))
  open SC M AA AA.A
in

(* misc *)
fun gen_is_gcs_finished get_gcsd = get_gcsd >>> GCSD.get_gclusters >>> arr GCS.is_finished

(* copy *)
(** make copy **)
fun gen_copy_cpfocus move_cpos init_copy (cpos, focus) zipper3 =
  move_cpos cpos >>> init_copy zipper3 focus

fun gen_copy_cpfocuss foldM copy_cpfocus cpfs x = foldM (fn cpf => AE.try (copy_cpfocus cpf x)) cpfs

fun gen_copy_update_focus copy_cpfocuss focus = (fn cud => copy_cpfocuss (cud focus)) |> mk_copy

(* actions *)
fun init_result_update_data set_gcs set_gc_list rud =
  let val (f, (gcs, gc_list)) = TR.init_result_update_data rud
  in set_gcs gcs >>> set_gc_list gc_list >>> arr (pair f) end

type cud = F.focus -> (int * F.focus) list

fun gen_update_result_update_data set_gcs set_gc_list foldM get_parent_actions get_copy_data =
  AU.update_result (init_result_update_data set_gcs set_gc_list) get_parent_actions
    (gen_copy_parent_actions foldM get_copy_data)

(** action priorities **)
fun Kupdate_prio_co update_prio p =
  (first (K p) &&& arr (fn _ => Kupdate_prio_co update_prio (update_prio p)))
  |> CO.coroutine

end

end
