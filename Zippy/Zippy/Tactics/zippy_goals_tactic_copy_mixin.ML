(*  Title:      Zippy/zippy_goals_tactic_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_COPY_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE

  val focus_list_apply_copy_update_data : Copy.copy_update_data -> (Tac.GPU.F.focus * 'a) list ->
    (GClusters.GCS.cluster_pos * (Tac.GPU.F.focus * 'a) list) list
end

functor Zippy_Goals_Tactic_Copy_Mixin(
    GTC : ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
  ) : ZIPPY_GOALS_TACTIC_COPY_MIXIN =
struct

open GTC

fun focus_list_apply_copy_update_data cud =
  Library.maps (fn (focus, x) => cud focus
    |> List.map (fn (cpos, focus) => (cpos, (focus, x))))
  #> partition_eq (eq_fst (op =))
  #> List.map (fn xs => (fst (hd xs), List.map snd xs))

end

