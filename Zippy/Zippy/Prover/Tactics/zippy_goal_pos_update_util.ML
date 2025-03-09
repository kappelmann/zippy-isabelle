(*  Title:      HOCLP/zippy_goal_pos_update_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GPOS_UPDATE_UTIL =
sig
  include ZIPPY_GPOS_UPDATE
  structure F : ZIPPY_FOCUS
  sharing type F.GCS.gcpos = GCS.gcpos
  sharing type F.GCS.gclusters = GCS.gclusters

  val update_focus : int -> GCS.gcpos gpos_update -> F.focus -> (GCS.cluster_pos * F.focus) list
end

functor Zippy_GPos_Update_Util(
    structure GPU : ZIPPY_GPOS_UPDATE
    structure F : ZIPPY_FOCUS
    sharing type F.GCS.gcpos = GPU.GCS.gcpos
    sharing type F.GCS.gclusters = GPU.GCS.gclusters
  ) : ZIPPY_GPOS_UPDATE_UTIL =
struct

structure F = F
open GPU

local
structure SA = SArrow_Arrow_Apply
fun dest_gcpos_update gcpos_update gpos = gcpos_update gpos
  |> T.map (SA.A.&&& (GCS.get_gcpos_cluster, GCS.get_gcpos_goal))
in
fun update_focus _ gcpos_update (F.Goals gpos) =
      map (dest_gcpos_update gcpos_update #> (fn T.Target gcposs => gcposs)) gpos
      |> flat
      |> partition_eq (fst #> (op =))
      |> map (SA.A.&&& (hd #> fst, map snd #> sort int_ord #> F.Goals))
  | update_focus ngclusters _ F.None = fold_range (rpair F.none #> cons) ngclusters []
end

end