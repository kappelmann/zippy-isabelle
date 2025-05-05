(*  Title:      Zippy/zippy_lists_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_BASE =
sig
  structure ZCOREAZ1 : \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close>

  structure ZCOREAZ2 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  sharing type ZCOREAZ2.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ2.ZD.L.lens = ZCOREAZ1.ZD.L.lens

  structure ZCOREAZ3 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  sharing type ZCOREAZ3.LI.M.exn = ZCOREAZ2.LI.M.exn
  sharing type ZCOREAZ3.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ3.ZD.L.lens = ZCOREAZ1.ZD.L.lens

  structure ZCOREAZ4 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  sharing type ZCOREAZ4.LI.M.exn = ZCOREAZ2.LI.M.exn
  sharing type ZCOREAZ4.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ4.ZD.L.lens = ZCOREAZ1.ZD.L.lens

  structure ZCOREAZ5 : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  where type 'a LI.t = 'a list
  sharing type ZCOREAZ5.LI.M.exn = ZCOREAZ2.LI.M.exn
  sharing type ZCOREAZ5.M.t = ZCOREAZ1.M.t
  sharing type ZCOREAZ5.ZD.L.lens = ZCOREAZ1.ZD.L.lens

  include ZIPPY_NODE_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZCORE.A.Z{i}.ZM.container = @{AllT_args} ZCOREAZ{i}.ZM.container
  where type @{AllT_args} ZCORE.A.Z{i}.ZD.content = @{AllT_args} ZCOREAZ{i}.ZD.content
  where type @{AllT_args} ZCORE.A.Z{i}.ZD.zcontext = @{AllT_args} ZCOREAZ{i}.ZD.zcontext\<close>\<close>
  sharing type M.t = ZCOREAZ1.M.t
  sharing type L.lens = ZCOREAZ1.ZD.L.lens
end

functor Zippy_Lists_Base(
    M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
    where type @{ParaT_args encl = "(" ")"} exn = unit
  ) :
    ZIPPY_LISTS_BASE
    \<^imap>\<open>\<open>{i}\<close> => \<open>where type @{AllT_args} ZCORE.N{i}.content = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
  =
struct

structure U = Zippy_Monad_Util(M); open U
structure U = Zippy_Monad_Exception_Util(M); open U

structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens_Kleisli"\<close>(
  structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens"\<close>(
    structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens_Base"\<close>(AA)
    structure A = A)
  structure K = A.K)

structure ZCOREAZ1 = \<^eval>\<open>sfx_T_nargs "Single_Content_Zipper"\<close>(
  structure AE = AE
  structure L = L
  type @{AllT_args} container = @{ZipperT_arg 0}
  type @{AllT_args} content = @{ZipperT_arg 0}
  val zip = M.pure
  val unzip = M.pure)

structure LZ = \<^eval>\<open>sfx_T_nargs "List_Zipper"\<close>(
  structure L = L
  structure LI = \<^eval>\<open>sfx_ParaT_nargs "GList"\<close>(M)
  type @{AllT_args} content = @{ZipperT_arg 0}
  fun mk_exn_horizontal x = A.K () x)
structure ZCOREAZ2 = LZ
structure ZCOREAZ3 = LZ
structure ZCOREAZ4 = LZ
structure ZCOREAZ5 = LZ

structure ZCORE = \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
  \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>structure Z{i} = ZCOREAZ{i}\<close>\<close>))
open ZCORE

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ZCOREAZ{i} = struct open ZCOREAZ{i} ZCORE.A.Z{i} end

structure ZCORE_CO{i} = \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
  structure L = L
  type @{AllT_args} container = @{AllT_args} Z{i}.ZD.content
  type @{AllT_args} data = @{AllT_args} container
  fun lens _ = L.id ()
)\<close>\<close>

end
