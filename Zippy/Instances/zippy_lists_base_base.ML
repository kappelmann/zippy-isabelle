(*  Title:      Zippy/zippy_lists_base_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_BASE_BASE =
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

  include ZIPPY_BASE_BASE
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZCORE.A.Z{i}.ZM.container = @{AllT_args} ZCOREAZ{i}.ZM.container
  where type @{AllT_args} ZCORE.A.Z{i}.ZD.content = @{AllT_args} ZCOREAZ{i}.ZD.content
  where type @{AllT_args} ZCORE.A.Z{i}.ZD.zcontext = @{AllT_args} ZCOREAZ{i}.ZD.zcontext\<close>\<close>
  sharing type M.t = ZCOREAZ1.M.t
  sharing type L.lens = ZCOREAZ1.ZD.L.lens
end
