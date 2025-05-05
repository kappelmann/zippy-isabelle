(*  Title:      Zippy/zippy_action_app_num_mixin_base.ML
    Author:     Kevin Kappelmann

Action application numbers.
*)
signature ZIPPY_ACTION_APP_NUM_MIXIN_BASE =
sig
  structure ACTIONAN : ZIPPY_ACTION_APP_NUM

  structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = ACTIONAN.action_app_num
end
