\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippy\<close>
theory Zippy_Base
  imports
    ML_Unification.ML_Logger
    ML_Unification.Setup_Result_Commands
    ML_Typeclasses.ML_Lenses
begin

paragraph \<open>Summary\<close>
text \<open>Zippy is a proof-search framework based on (alternating) zippers.\<close>

setup_result zippy_logger = \<open>Logger.new_logger Logger.root "Zippy"\<close>

ML\<open>
signature LIFT_DATA_BASE =
sig
  structure AF : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
  structure AT : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_BASE"\<close>
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  where type (@{ParaT_args} 'g, 'b) C.cat = (@{ParaT_args} 'g, 'b) AT.cat
  val lift : (@{ParaT_args} 'g, 'b) AF.cat -> (@{ParaT_args} 'g, 'b) AT.cat
end
\<close>

end
