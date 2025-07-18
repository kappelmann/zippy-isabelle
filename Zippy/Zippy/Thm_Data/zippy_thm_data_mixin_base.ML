(*  Title:      Zippy/zippy_thm_data_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_THM_DATA_MIXIN_BASE =
sig
  include ZIPPY_LOGGER_MIXIN_BASE
  type data
  val eq_data : data * data -> bool
  val pretty_data : Proof.context -> data -> Pretty.T

  structure Data : GENERIC_TERM_INDEX_DATA
  where type value = {thm : thm, data : data}
end

functor Zippy_Thm_Data_Mixin_Base(A :
  sig
    structure FI : FUNCTOR_INSTANCE_BASE
    structure Log : ZIPPY_LOGGER_MIXIN_BASE
    structure TI : TERM_INDEX
    type data
    val eq_data : data * data -> bool
    val pretty_data : Proof.context -> data -> Pretty.T
  end
  ) : ZIPPY_THM_DATA_MIXIN_BASE =
struct
open A A.Log
structure FI = Functor_Instance(FI)
\<^functor_instance>\<open>struct_name = Data
  and functor_name = Generic_Term_Index_Data
  and id = \<open>FI.id\<close>
  and path = \<open>FI.long_name\<close>
  and more_args = \<open>
    val parent_logger = Log.logger
    structure TI = TI
    type value = {thm : thm, data : data}
    fun eq_value ({thm = thm1, data = d1}, {thm = thm2, data = d2}) =
      Thm.eq_thm (thm1, thm2) andalso eq_data (d1, d2)
    fun pretty_value ctxt {thm, data} = SpecCheck_Show.record [
      ("thm", Thm.pretty_thm ctxt thm),
      ("data", pretty_data ctxt data)
    ]\<close>\<close>
end
