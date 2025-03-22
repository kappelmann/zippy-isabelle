(*  Title:      HOCLP/alternating_zipper_nodes_zippers.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
    sharing type Z{i}.ZO.L.lens = Z1.ZO.L.lens
    sharing type Z{i}.M.t = Z1.M.t\<close>\<close>

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} ncontent{i} (*content for node{i}*)
    val ncontent{i} : (@{ParaT_args} @{AllT_args} Z{i}.ZO.content, @{AllT_args} ncontent{i}) Z1.cat\<close>\<close>

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val next{i} : (@{ParaT_args} @{AllT_args} Z{i}.ZO.content, (@{ParaT_args}
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.M.t) Z1.cat\<close>\<close>

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val content{i} : @{AllT_args} ncontent{i} -> (@{ParaT_args} (@{ParaT_args}
      @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.M.t,
      @{AllT_args} Z{i}.ZO.content) Z1.cat\<close>\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZO.zcontext = @{AllT_args} Z{i}.ZO.zcontext
    where type @{AllT_args} Z{i}.ZM.container = @{AllT_args} Z{i}.ZM.container
    where type @{AllT_args} Z{i}.zipper = @{AllT_args} Z{i}.zipper\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} N{i}.content = @{AllT_args} ncontent{i}\<close>\<close>
    where type (@{ParaT_args} 'a) Z1.M.t = (@{ParaT_args} 'a) Z1.M.t
    where type (@{ParaT_args} 't, 'o, 's, 'i) Z1.ZO.L.lens = (@{ParaT_args} 't, 'o, 's, 'i) Z1.ZO.L.lens
  =
struct
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(Z1.M)
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(Z1.M)

structure Base = struct structure A = A; structure L = Z1.ZO.L end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>sfx_T_nargs "Node"\<close>(open Base
  type @{AllT_args} content = @{AllT_args} ncontent{i}
  type @{AllT_args} next = (@{ParaT_args}
    @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>M.t
)\<close>\<close>
structure Base = struct
  structure AF = \<^eval>\<open>sfx_ParaT_nargs "SArrow_Arrow_Apply" ^ ".A"\<close>
  structure AT = A
  structure L = Z1.ZO.L
  fun lift a = AT.arr a
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>sfx_T_nargs "Lift_Node"\<close>(
  open Base; structure N = N{i})\<close>\<close>

structure Base = struct structure A = A; open A end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Replace_Zipper_Content"\<close>(
  open Base
  structure Z = Z{i}
  type @{AllT_args} ncontent = @{AllT_args} N{i}.node
  fun ncontent x = x |> comp N{i}.node (ncontent{i} &&& next{i})
  fun dest_ncontent x = x |> comp (AA.uncurry content{i}) (N{i}.get_content &&& N{i}.get_next)
)\<close>\<close>

end
