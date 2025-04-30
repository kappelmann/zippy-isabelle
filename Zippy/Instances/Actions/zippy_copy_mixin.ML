(*  Title:      Zippy/zippy_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COPY_MIXIN =
sig
  include ZIPPY_COPY_MIXIN_BASE

  (* copy *)
  (** run copies **)
  val get_run_copy : copy_update_data -> @{AllT_args} zipper_from ->
    (@{ParaT_args} @{AllT_args} zipper_to) hom_move

  val gen_copy_parent_actions :
    (*foldM*)
    (('pa -> (@{ParaT_args} 'z) hom_move) -> 'pas -> (@{ParaT_args} 'z) hom_move) ->
    (*copy parent action*)
    ('cud -> 'pa -> (@{ParaT_args} 'z) hom_move) ->
    'cud -> 'pas -> (@{ParaT_args} 'z) hom_move

  val copy_parent_actions :
    ((@{AllT_args} zipper_from -> (@{ParaT_args} @{AllT_args} zipper_to) hom_move) ->
      'zs -> (@{ParaT_args} 'z) hom_move) ->
    copy_update_data -> 'zs -> (@{ParaT_args} 'z) hom_move
end

functor Zippy_Copy_Mixin(
    structure Z : ZIPPY_BASE
    structure COPY : ZIPPY_COPY_MIXIN_BASE
    sharing type COPY.zipper_from = Z.Z3.zipper
    sharing type COPY.zipper_to = Z.Z1.zipper
    sharing type COPY.M.t = Z.M.t
    sharing type COPY.L.lens = Z.L.lens
  ) : ZIPPY_COPY_MIXIN =
struct

open Z COPY

local open SC MO
in
(* copy *)
(** run copies **)
fun get_run_copy cud z3 z1 = L.getter z3
  >>= (run_copy #> (fn copy => copy cud z3 z1))

fun gen_copy_parent_actions foldM copy_parent_action cud =
  foldM (fn ac => AE.try (copy_parent_action cud ac))

fun copy_parent_actions foldM = gen_copy_parent_actions foldM get_run_copy
end

end

