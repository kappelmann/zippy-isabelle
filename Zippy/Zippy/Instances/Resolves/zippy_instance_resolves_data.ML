(*  Title:      Zippy/zippy_instance_resolves_data.ML
    Author:     Kevin Kappelmann
*)
functor Zippy_Instance_Resolves_Data(
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Z : ZIPPY_INSTANCE_RESOLVE
    structure TI : TERM_INDEX
    val init_args : (int -> @{AllT_args} Z.Base_Data.PAction.action,
      Z.Base_Data.GCS.goal_pos -> (@{ParaT_args} @{AllT_args} Z.ZLP.Z2.zipper) Z.emorph,
      @{AllT_args} Z.Result_Action.mk_copy_update_data,
      Z.Base_Data.AAMeta.P.progress,
      @{AllT_args} Z.PResults.prio_sq_co,
      term * @{AllT_args} Z.Resolve.data -> bool) Zippy_Instance_Resolve_Data_Args.PCA.entries
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
  ) =
struct
local structure FI =  Functor_Instance(FI)
in
structure Logging =
struct
  local structure Base = struct val parent_logger = Log.logger end
  in
  structure Resolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "Resolve_Unif")
  structure Resolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "Resolve_Match")
  structure EResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "EResolve_Unif")
  structure EResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "EResolve_Match")
  structure DResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "DResolve_Unif")
  structure DResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "DResolve_Match")
  structure FResolve_Unif = Zippy_Logger_Mixin_Base(open Base; val name = "FResolve_Unif")
  structure FResolve_Match = Zippy_Logger_Mixin_Base(open Base; val name = "FResolve_Match")
  end
end

local open Z; open ZLP
  structure Base = struct structure Z = Z; structure TI = TI; val init_args = init_args end
in
\<^functor_instance>\<open>struct_name: Resolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "resolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.Resolve_Unif\<close>\<close>
structure Resolve_Unif = Resolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: Resolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "resolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.concl_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.Resolve_Match\<close>\<close>
structure Resolve_Match = Resolve_Match.Resolve_Data

\<^functor_instance>\<open>struct_name: EResolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "eresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of #> General_Util.pred
    structure Log = Logging.EResolve_Unif\<close>\<close>
structure EResolve_Unif = EResolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: EResolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "eresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of #> General_Util.pred
    structure Log = Logging.EResolve_Match\<close>\<close>
structure EResolve_Match = EResolve_Match.Resolve_Data

\<^functor_instance>\<open>struct_name: DResolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "dresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.DResolve_Unif\<close>\<close>
structure DResolve_Unif = DResolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: DResolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "dresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.DResolve_Match\<close>\<close>
structure DResolve_Match = DResolve_Match.Resolve_Data

\<^functor_instance>\<open>struct_name: FResolve_Unif
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "fresolve_unif"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.FResolve_Unif\<close>\<close>
structure FResolve_Unif = FResolve_Unif.Resolve_Data
\<^functor_instance>\<open>struct_name: FResolve_Match
  functor_name: Zippy_Instance_Resolve_Data
  FI_struct_name: FI_Resolve_Data
  id: \<open>FI.prefix_id "fresolve_match"\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>open Base
    val key_of_thm = Thm.major_prem_of
    val num_new_goals = Thm.nprems_of
    structure Log = Logging.FResolve_Match\<close>\<close>
structure FResolve_Match = FResolve_Match.Resolve_Data
end
end
end
