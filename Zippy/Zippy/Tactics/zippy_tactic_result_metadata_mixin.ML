(*  Title:      Zippy/zippy_tactic_result_metadata_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_RESULT_METADATA_MIXIN =
sig
  include ZIPPY_TACTIC_RESULT_METADATA_MIXIN_BASE

  structure Progress : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} L.container
  where type @{AllT_args} data = Meta.progress
end

functor Zippy_Tactic_Result_Metadata_Mixin(
    Tac_Result_Meta : ZIPPY_TACTIC_RESULT_METADATA_MIXIN_BASE
  ) : ZIPPY_TACTIC_RESULT_METADATA_MIXIN =
struct

open Tac_Result_Meta

structure Progress = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = L; structure L2 = Meta.Progress)

end
