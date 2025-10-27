(*  Title:      Zippy/zippy_cost_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_COST_MIXIN_BASE =
sig
  type cost

  structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = cost
end

functor Zippy_Cost_Mixin_Base(A :
  sig
    type cost
    structure L : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
    where type @{AllT_args} data = cost
  end
  ) : ZIPPY_COST_MIXIN_BASE
  = A