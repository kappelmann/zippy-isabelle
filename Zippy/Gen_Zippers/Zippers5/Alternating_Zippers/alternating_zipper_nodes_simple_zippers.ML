(*  Title:      HOCLP/alternating_zipper_nodes_simple_zippers.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    where type @{AllT_args} ZO.content = @{ZipperT_arg 0}
    sharing type Z{i}.ZO.L.lens = Z1.ZO.L.lens
    sharing type Z{i}.M.t = Z1.M.t\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} ncontent{i} (*content for node{i}*)\<close>\<close>
  ) :
  sig
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} node{i}\<close>\<close>

    include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args} @{AllT_args} node{i},
      @{ZipperT_args start = 1}) Z{i}.ZM.container
    where type @{AllT_args} N{i}.node = @{AllT_args} node{i}
    where type @{AllT_args} N{i}.content = @{AllT_args} ncontent{i}
    \<close>\<close>
    (* where @{AllT_args} Zi.ZO.zcontext = (@{ParaT_args} @{AllT_args} Ni.node, 'a2, ...) Zi.ZO.zcontext *)
    where type (@{ParaT_args} 'a) Z1.M.t = (@{ParaT_args} 'a) Z1.M.t
    where type (@{ParaT_args} 't, 'o, 's, 'i) Z1.ZO.L.lens =
      (@{ParaT_args} 't, 'o, 's, 'i) Z1.ZO.L.lens
  end
  =
struct

structure Base = struct type (@{AllT_args encl = "" ""}, 'n) next = 'n end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>succ_node_functor\<close>(
  open Base
  type (@{AllT_args encl = "" ""}, 'n) content = @{AllT_args} ncontent{i})\<close>\<close>
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z1.M)
structure Base = struct
  structure AF = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply" ^ ".A"\<close>
  structure AT = A
  structure L = Z1.ZO.L
  fun lift a = AT.arr a
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = Lift_\<^eval>\<open>succ_node_functor\<close>(
  open Base; structure N = N{i})\<close>\<close>

datatype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} next{i} = Next{i} of (@{ParaT_args}
  (@{ParaT_args}
    (@{AllT_args encl = "" ","} @{AllT_args} next\<^eval>\<open>succ_mod_nzippers {i}\<close>)
      N\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>node,
    @{ZipperT_args start = 1})
  Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.ZM.Zip.M.t\<close>
where sep = "and"\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun next{i} x = Next{i} x
fun dest_next{i} (Next{i} x) = x\<close>\<close>

structure Base =
struct
\<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} inst{i} = @{ZipperT_arg \<open>{i} - 1\<close>}\<close>\<close>
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} =
\<^eval>\<open>sfx_T_nargs "Modify_Node_Succ"\<close>(
  open Base
  type @{AllT_args} inst\<^eval>\<open>string_of_int (ML_Gen.ZipperT_nargs () + 1)\<close> =
    @{AllT_args} next{i}
  structure N = N{i}
)\<close>\<close>

structure Base =
struct
\<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} inst{i} = @{ZipperT_arg \<open>{i} - 1\<close>}\<close> where start = 2\<close>
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Instantiate_Zipper"\<close>(
  open Base
  type @{AllT_args} inst1 = @{AllT_args} N{i}.node
  structure Z = Z{i}
)\<close>\<close>

structure Base =
struct
  structure A = A
  fun ncontent x = x |> A.id ()
  fun dest_ncontent x = x |> A.id ()
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>sfx_T_nargs "Replace_Node_Content_Next"\<close>(
  open Base
  structure N = N{i}
  type @{AllT_args} ncontent = @{AllT_args} ncontent{i}
  type @{AllT_args} nnext = (@{ParaT_args}
    @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next{i}
  fun dest_nnext x = x |> A.arr next{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} node{i} = @{AllT_args} N{i}.node\<close>\<close>

end