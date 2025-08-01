(*  Title:      Zippy/zippy_resolve_action_data_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_RESOLVE_ACTION_DATA_MIXIN_BASE =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  structure Data : GENERIC_TERM_INDEX_DATA
  where type value = @{AllT_args} Zippy.Tac_Util.resolve_action_data
end

functor Zippy_Resolve_Action_Data_Mixin_Base(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure TI : TERM_INDEX
  end
  ) : ZIPPY_RESOLVE_ACTION_DATA_MIXIN_BASE =
struct
open A A.Log
structure FI = Functor_Instance(FI)
\<^functor_instance>\<open>struct_name: Data
  functor_name: Generic_Term_Index_Data
  id: \<open>FI.id\<close>
  path: \<open>FI.long_name\<close>
  more_args: \<open>
    val parent_logger = Log.logger
    structure TI = TI
    type value = @{AllT_args} Zippy.Tac_Util.resolve_action_data
    val eq_value = Zippy.Tac_Util.eq_resolve_action_data
    val pretty_value = Zippy.Tac_Util.pretty_resolve_action_data\<close>\<close>
end
