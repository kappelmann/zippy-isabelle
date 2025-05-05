(*  Title:      Zippy/zippy_node_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE_BASE =
sig
  include ZIPPY_BASE_BASE

  (*zipper containing the core data*)
  structure ZCORE : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
  sharing type ZCORE.M.t = M.t
  sharing type ZCORE.L.lens = L.lens

  (*lenses for core data*)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure ZCORE_CO{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type ZCORE_CO{i}.container = Z{i}.ZD.content
  sharing type ZCORE_CO{i}.data = ZCORE.Z{i}.ZD.content
  sharing type ZCORE_CO{i}.lens = L.lens
  sharing type ZCORE_CO{i}.K.M.t = M.t\<close>\<close>
end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Instantiate_Zippy_Node_Base(
    type @{AllT_args} inst
    structure Z : ZIPPY_NODE_BASE
  ) :
    ZIPPY_NODE_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCORE.A.Z{i}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.A.Z{i}.ZM.container
    where type @{AllT_args} ZCORE.A.Z{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.A.Z{i}.ZD.content
    where type @{AllT_args} ZCORE.A.Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.A.Z{i}.ZD.zcontext
    where type @{AllT_args} ZCORE.A.Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.A.Z{i}.zipper
    where type @{AllT_args} ZCORE.A.N{i}.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.A.N{i}.content
    where type @{AllT_args} ZCORE.Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.Z{i}.zipper
    where type @{AllT_args} ZCORE.zcontext{i} = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.zcontext{i}
    where type @{AllT_args} ZCORE.pzipper{i} = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCORE.pzipper{i}
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.ZD.content
    where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.zipper\<close>\<close>
  = Z\<close>\<close>