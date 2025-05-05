(*  Title:      Zippy/zippy_goal_cluster_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER_MIXIN_BASE =
sig
  structure GC : ZIPPY_GOAL_CLUSTER

  structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = GC.gcluster
end
