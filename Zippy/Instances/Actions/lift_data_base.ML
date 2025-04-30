(*  Title:      Zippy/lift_data_base.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_ParaT_nargs "LIFT_DATA_BASE"\<close> =
sig
  structure AF : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
  structure AT : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_BASE"\<close>
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) AT.cat
  val lift : (@{ParaT_args} 'a, 'b) AF.cat -> (@{ParaT_args} 'a, 'b) AT.cat
end
