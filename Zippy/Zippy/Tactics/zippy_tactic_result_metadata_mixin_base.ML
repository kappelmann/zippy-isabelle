(*  Title:      Zippy/zippy_tactic_result_metadata_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_RESULT_METADATA_MIXIN_BASE =
sig
  structure Meta : ZIPPY_TACTIC_RESULT_METADATA
  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = Meta.metadata
end

functor Zippy_Tactic_Result_Metadata_Mixin_Base(A :
  sig
    structure Meta : ZIPPY_TACTIC_RESULT_METADATA
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = Meta.metadata
  end) : ZIPPY_TACTIC_RESULT_METADATA_MIXIN_BASE
  = A
