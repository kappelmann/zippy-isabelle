(*  Title:      Zippy/zippy_goals_tactic_copy_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_TACTIC_COPY_MIXIN_BASE =
sig
  include ZIPPY_GOALS_TACTIC_MIXIN_BASE

  structure COPY : ZIPPY_COPY_MIXIN_BASE
  where type copy_update_data = TAC.GPU.F.focus -> (GCS.GCS.cluster_pos * TAC.GPU.F.focus) list
  sharing type COPY.M.t = M.t
  sharing type COPY.L.lens = GCS.L.lens
end
