(*  Title:      Zippy/zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} zipper
  structure ZM : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
  sharing type ZM.zipper = zipper
  sharing type ZM.M.t = M.t
  structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  sharing type ZD.zipper = zipper
end

functor \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
    structure ZM : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    structure ZD : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD.zipper = ZM.zipper
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close> =
struct
structure ZM = ZM
structure ZD = ZD
open ZM
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>sfx_inst_T_nargs "Instantiate_Zipper" {i}\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.ZM.container
    where type @{AllT_args} ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.ZD.content
    where type @{AllT_args} ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.ZD.zcontext
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.zipper
  = Z\<close>\<close>
