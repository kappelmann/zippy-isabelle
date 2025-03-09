(*  Title:      HOCLP/alternating_zippers_nodes_zippers.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes_Base_Args_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    sharing type Z{i}.ZO.L.lens = Z1.ZO.L.lens
    sharing type Z{i}.M.t = Z1.M.t\<close>\<close>

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{T_args} ncontent{i} (*content for node{i}*)
    val ncontent{i} : (@{ParaT_args}, @{T_args} Z{i}.ZO.content, @{T_args} ncontent{i}) Z1.cat\<close>\<close>

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val next{i} : (@{ParaT_args}, @{T_args} Z{i}.ZO.content, (@{ParaT_args},
      @{T_args} Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.container) Z{i}.M.t) Z1.cat\<close>\<close>

    \<^imap>\<open>\<open>{i}\<close> => \<open>
    val content{i} : @{T_args} ncontent{i} -> (@{ParaT_args}, (@{ParaT_args},
      @{T_args} Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.container)
        Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>M.t,
      @{T_args} Z{i}.ZO.content) Z1.cat\<close>\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.ZO.zcontext = @{T_args} Z{i}.ZO.zcontext
    where type @{T_args} Z{i}.ZM.container = @{T_args} Z{i}.ZM.container
    where type @{T_args} Z{i}.zipper = @{T_args} Z{i}.zipper\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} N{i}.content = @{T_args} ncontent{i}\<close>\<close>
    where type ('p1, 'a) Z1.M.t = ('p1, 'a) Z1.M.t
    where type ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
  =
struct
structure A = Kleisli_Arrow(Z1.M)
structure AA = Kleisli_Arrow_Apply(Z1.M)

structure Base = struct structure A = A; structure L = Z1.ZO.L end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Node"\<close>(open Base
  type @{T_args} content = @{T_args} ncontent{i}
  type @{T_args} next = (@{ParaT_args},
    @{T_args} Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>M.t
)\<close>\<close>
structure Base = struct structure AF = SArrow_Arrow_Apply.A; structure AT = A; structure L = Z1.ZO.L;
  fun lift a = AT.arr a end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Lift_Node"\<close>(
  open Base; structure N = N{i})\<close>\<close>

structure Base = struct structure A = A; open A end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Zipper" ^ "_Content"\<close>(
  open Base
  structure Z = Z{i}
  type @{T_args} ncontent = @{T_args} N{i}.node
  fun ncontent x = x |> comp N{i}.node (ncontent{i} &&& next{i})
  fun dest_ncontent x = x |> comp (AA.uncurry content{i}) (N{i}.get_content &&& N{i}.get_next)
)\<close>\<close>

end
