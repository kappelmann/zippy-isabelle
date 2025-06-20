(*  Title:      Zippy/zippy_tactic_result_metadata.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_TACTIC_RESULT_METADATA =
sig
  type progress = Zippy_Tactic_Result_Progress.progress

  type metadata
  val metadata : progress -> metadata

  val eq_metadata : metadata * metadata -> bool
  val pretty_metadata : metadata -> Pretty.T

  structure Progress : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = metadata
  where type @{AllT_args} data = progress

  val add : metadata * metadata -> metadata
end

structure Zippy_Tactic_Result_Metadata : ZIPPY_TACTIC_RESULT_METADATA =
struct

type progress = Zippy_Tactic_Result_Progress.progress

datatype metadata = Metadata of {
  progress : progress
}
fun metadata progress = Metadata {progress = progress}

fun eq_metadata (m1 as Metadata {progress = progress1}, m2 as Metadata {progress = progress2}) =
  pointer_eq (m1, m2) orelse progress1 = progress2
fun pretty_metadata (Metadata {progress}) = SpecCheck_Show_Base.record [
    ("progress", Zippy_Tactic_Result_Progress.pretty progress)
  ]

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>
structure Base = struct open L; type @{AllT_args} container = metadata end
structure Progress =
struct
  open Base
  type @{AllT_args} data = progress
  fun getter (Metadata {progress,...}) = progress
  fun modifier (f, (Metadata {progress})) = Metadata {progress = f progress}
  fun lens _ = L.mk_lens getter modifier
end

local open Zippy_Tactic_Result_Progress
in
fun add (md1, md2) =
  let val progress =
    if forall (equal promising) (List.map Progress.getter [md1, md2])
    then promising else unclear
  in metadata progress end
end

end
