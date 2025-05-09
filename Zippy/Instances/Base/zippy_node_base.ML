(*  Title:      Zippy/zippy_node_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE_BASE =
sig
  include ZIPPY_BASE_BASE

  (*zipper containing the core data*)
  structure ZCore : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
  sharing type ZCore.M.t = M.t

  (*lenses for core data*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZCore_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type ZCore_Co{i}.container = Z{i}.ZD.content
  sharing type ZCore_Co{i}.data = ZCore.Z{i}.ZD.content\<close>\<close>
end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Instantiate_Zippy_Node_Base_{j}(
    type @{AllT_args} inst
    structure Z : ZIPPY_NODE_BASE
  ) :
    ZIPPY_NODE_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCore.A.Z{i}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.A.Z{i}.ZM.container
    where type @{AllT_args} ZCore.A.Z{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.A.Z{i}.ZD.content
    where type @{AllT_args} ZCore.A.Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.A.Z{i}.ZD.zcontext
    where type @{AllT_args} ZCore.A.Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.A.Z{i}.zipper
    where type @{AllT_args} ZCore.A.N{i}.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.A.N{i}.content
    where type @{AllT_args} ZCore.Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.Z{i}.zipper
    where type @{AllT_args} ZCore.zcontext{i} = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.zcontext{i}
    where type @{AllT_args} ZCore.pzipper{i} = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore.pzipper{i}
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.ZD.content
    where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.zipper\<close>\<close>
  = Z\<close>\<close>
