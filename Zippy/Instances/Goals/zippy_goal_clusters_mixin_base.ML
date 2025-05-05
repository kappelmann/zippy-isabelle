(*  Title:      Zippy/zippy_goal_clusters_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTERS_MIXIN_BASE =
sig
  structure GCS : ZIPPY_GOAL_CLUSTERS

  structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = GCS.gclusters
end
