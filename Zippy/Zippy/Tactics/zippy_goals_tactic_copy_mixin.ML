(*  Title:      Zippy/zippy_goals_tactic_copy_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_COPY_MIXIN =
sig
  include ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE

  val apply_copy_update_data_focus_list : Copy.copy_update_data -> ('a * Tac.GPU.F.focus) list ->
    (GClusters.GCS.cluster_pos * ('a * Tac.GPU.F.focus) list) list
end

functor Zippy_Goals_Tactic_Copy_Mixin(
    GTC : ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE
  ) : ZIPPY_GOALS_TACTIC_COPY_MIXIN =
struct

open GTC

fun apply_copy_update_data_focus_list cud =
  Library.maps (fn (x, focus) => cud focus
    |> List.map (fn (cpos, focus) => (cpos, (x, focus))))
  #> partition_eq (eq_fst (op =))
  #> List.map (fn xs => (fst (hd xs), List.map snd xs))

end

