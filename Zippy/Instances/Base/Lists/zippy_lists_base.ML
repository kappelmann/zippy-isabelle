(*  Title:      Zippy/zippy_lists_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_BASE =
sig
  structure ZCore_AZ1 : \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close>

  structure ZCore_AZ2 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZCore_AZ2.M.t = ZCore_AZ1.M.t

  structure ZCore_AZ3 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZCore_AZ3.M.t = ZCore_AZ1.M.t
  sharing type ZCore_AZ3.L.M.exn = ZCore_AZ2.L.M.exn

  structure ZCore_AZ4 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZCore_AZ4.M.t = ZCore_AZ1.M.t
  sharing type ZCore_AZ4.L.M.exn = ZCore_AZ2.L.M.exn

  structure ZCore_AZ5 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a L.t = 'a list
  sharing type ZCore_AZ5.M.t = ZCore_AZ1.M.t
  sharing type ZCore_AZ5.L.M.exn = ZCore_AZ2.L.M.exn

  include ZIPPY_NODE_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZCore.A.Z{i}.ZM.container = @{AllT_args} ZCore_AZ{i}.ZM.container
  where type @{AllT_args} ZCore.A.Z{i}.ZD.content = @{AllT_args} ZCore_AZ{i}.ZD.content
  where type @{AllT_args} ZCore.A.Z{i}.ZD.zcontext = @{AllT_args} ZCore_AZ{i}.ZD.zcontext\<close>\<close>
  sharing type M.t = ZCore_AZ1.M.t
end

functor Zippy_Lists_Base(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl = "(" ")"} exn = unit
  ) :
    ZIPPY_LISTS_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>where type @{AllT_args} ZCore.N{i}.content = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
  =
struct

structure U = Zippy_Monad_Util(M); open U
structure U = Zippy_Monad_Exception_Util(M); open U

structure ZCore_AZ1 = \<^eval>\<open>sfx_T_nargs "Single_Content_Zipper"\<close>(
  structure AE = AE
  type @{AllT_args} container = @{ZipperT_arg 0}
  type @{AllT_args} content = @{ZipperT_arg 0}
  val zip = M.pure
  val unzip = M.pure)

structure LZ = \<^eval>\<open>sfx_T_nargs "List_Zipper"\<close>(
  structure L = \<^eval>\<open>sfx_ParaT_nargs "GList"\<close>(M)
  type @{AllT_args} content = @{ZipperT_arg 0}
  fun mk_exn_horizontal x = A.K () x)
structure ZCore_AZ2 = LZ
structure ZCore_AZ3 = LZ
structure ZCore_AZ4 = LZ
structure ZCore_AZ5 = LZ

structure ZCore = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
  \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>structure Z{i} = ZCore_AZ{i}\<close>\<close>))
open ZCore

(*instantiate the base zippers*)
structure ZCore_AZ1 : \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} ZCore.A.Z1.ZM.container
  where type @{AllT_args} ZD.content = @{AllT_args} ZCore.A.Z1.ZD.content
= ZCore_AZ1

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZCore_AZ{i} : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type @{AllT_args} ZD.content = @{AllT_args} ZCore.A.Z{i}.ZD.content
= struct open ZCore_AZ{i} ZCore.A.Z{i} end\<close>
where start = 2\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZCore_Co{i} = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  type @{AllT_args} container = @{AllT_args} Z{i}.ZD.content
  type @{AllT_args} data = @{AllT_args} container
  fun lens _ = \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".id"\<close> ()
)\<close>\<close>

end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Instantiate_Zippy_Lists_Base_{j}(
    type @{AllT_args} inst
    structure Z : ZIPPY_LISTS_BASE
  ) :
    ZIPPY_LISTS_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCore_AZ{i}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore_AZ{i}.ZM.container
    where type @{AllT_args} ZCore_AZ{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore_AZ{i}.ZD.content\<close>
    where stop = 1\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} ZCore_AZ{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore_AZ{i}.ZD.content
    where type @{AllT_args} ZCore_AZ{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.ZCore_AZ{i}.zipper\<close>
    where start = 2\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
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
  =  Z\<close>\<close>