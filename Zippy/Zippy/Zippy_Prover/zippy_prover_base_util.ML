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

  (* Z1 *)
  val get_gclusters_state : (@{ParaT_args}, @{T_args} Z1.zipper, GCS.state) cat
  val is_gclusters_finished : (@{ParaT_args}, @{T_args} Z1.zipper, bool) cat

  (* Z2 *)
  val get_gcluster_state : (@{ParaT_args}, @{T_args} Z2.zipper, GCS.state) cat

  (* copy *)
  (** make copy **)
  val gen_copy_cpfocus :
    (*move to cluster position*)
    ('cp -> ('p1, 'z1, 'z2) cat) ->
    (*initialise the copy*)
    ('z3 -> 'f -> ('p1, 'z2, 'z4) cat) ->
    ('cp * 'f) -> 'z3 -> ('p1, 'z1, 'z4) cat

  val gen_copy_cpfocuss :
(* (('a -> ('b, 'c, 'c) AE.cat) -> 'd -> 'e) -> *)
      (* ('a -> 'f -> ('b, 'c, 'c) AE.cat) -> 'd -> 'f -> 'e *)
    (*foldM*)
    (('cpf -> ('p1, @{T_args} Z1.zipper) hom_move) ->
      'cpfs -> ('p1, @{T_args} Z1.zipper) hom_move) ->
    ('cpf -> @{T_args} Z3.zipper -> ('p1, @{T_args} Z1.zipper) hom_move) ->
    'cpfs -> @{T_args} Z3.zipper -> ('p1, @{T_args} Z1.zipper) hom_move

  (*val gen_copy_update_focus :
    ('cpfs -> ('p1, 'f -> 'cpfs, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper3 ->
      ('p1, ('p1, 'f -> 'cpfs, 'p, 'r, 'a1, 'a2, 'a3, 'a4) zipper1) hom_move) ->
    'f -> ('p1, 'f -> 'cpfs, 'p, 'r, 'a1, 'a2, 'a3, 'a4) copy

  (* actions *)
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
  val Kupdate_prio_co : ('p -> 'p) -> 'p -> ('p1, 'x * 'sq, 'p * 'sq) CO.coroutine *)

end

functor Zippy_Prover_Base_Util(
    structure Z : ZIPPY_PROVER_BASE
    structure TR : ZIPPY_TACTIC_RESULT
    sharing type TR.GC.GCS.gcpos = Z.GCS.gcpos
    sharing type TR.GC.GCS.gclusters = Z.GCS.gclusters
    sharing type TR.GC.gcluster = Z.GC.gcluster
    sharing type TR.GPU.F.focus = Z.F.focus
  ) : ZIPPY_PROVER_BASE_UTIL =
struct

open Z

structure TR = TR

local structure SC = Semi_Category(Z); structure A = Kleisli_Arrow(M); open SC A
in

(* Z1 *)
fun get_gclusters x = x |> (L.get (gclusters ()))
fun get_gclusters_state x = x |> (get_gclusters >>> arr GCS.get_state)
fun is_gclusters_finished x = x |> (get_gclusters >>> arr GCS.is_finished)

(* Z2 *)
fun get_gcluster_state x = x |> (L.get (gcluster ()) >>> arr GC.get_state)

(* copy *)
(** make copy **)
fun gen_copy_cpfocus move_cpos init_copy (cpos, focus) zipper3 =
  move_cpos cpos >>> init_copy zipper3 focus
fun gen_copy_cpfocuss foldM copy_cpfocus cpfs x =
  foldM (fn cpf => AE.try (copy_cpfocus cpf x)) cpfs
fun gen_copy_update_focus copy_cpfocuss focus = (fn cud => copy_cpfocuss (cud focus)) |> mk_copy

(* actions *)
fun init_result_update_data set_gcs set_gc_list rud =
  let val (f, (gcs, gc_list)) = TR.init_result_update_data rud
  in set_gcs gcs >>> set_gc_list gc_list >>> arr (pair f) end

(* fun gen_update_result_update_data set_gcs set_gc_list foldM get_parent_actions get_copy_data =
  AU.update_result (init_result_update_data set_gcs set_gc_list) get_parent_actions
    (gen_copy_parent_actions foldM get_copy_data) *)

(** action priorities **)
fun Kupdate_prio_co update_prio p =
  (first (K p) &&& arr (fn _ => Kupdate_prio_co update_prio (update_prio p)))
  |> CO.coroutine

end

end
