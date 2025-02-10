(*  Title:      HOCLP/alternating_zippers_nodes_simple_zippers.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes_Base_Args_Simple_Zippers"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    structure Z{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    where type @{T_args} ZO.content = @{PolyT_arg 0}
    sharing type Z{i}.ZO.L.lens = Z1.ZO.L.lens
    sharing type Z{i}.M.t = Z1.M.t\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{T_args} ncontent{i} (*content for node{i}*)\<close>\<close>
  ) :
  sig
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{T_args} node{i}\<close>\<close>

    include \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.ZM.container = (@{ParaT_args}, @{T_args} node{i}
      @{PolyT_args start = 1 and encl = "," ""}) Z{i}.ZM.container
    where type @{T_args} N{i}.node = @{T_args} node{i}
    where type @{T_args} N{i}.content = @{T_args} ncontent{i}
    \<close>\<close>
    (* where @{T_args} Zi.ZO.zcontext = (@{ParaT_args}, @{T_args} Ni.node, 'a2, ...) Zi.ZO.zcontext *)
    where type ('p1, 'a) Z1.M.t = ('p1, 'a) Z1.M.t
    where type ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens = ('p1, 't, 'o, 's, 'i) Z1.ZO.L.lens
  end
  =
struct

structure Base = struct type (@{T_args encl = "" ""}, 'n) next = 'n end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = Node\<^eval>\<open>string_of_int (T_Args.Poly_nargs () + 1)\<close>(
  open Base
  type (@{T_args encl = "" ""}, 'n) content = @{T_args} ncontent{i})\<close>\<close>
structure A = Kleisli_Arrow(Z1.M)
structure Base = struct structure AF = SArrow_Arrow_Apply.A; structure AT = A; structure L = Z1.ZO.L;
  fun lift a = AT.arr a end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = Lift_Node6(open Base; structure N = N{i})\<close>\<close>

datatype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{T_args} next{i} = Next{i} of (@{ParaT_args},
  (@{ParaT_args},
  (@{T_args encl = "" ""}, @{T_args} next\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i}\<close>)
    N\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>node
  @{PolyT_args start = 1 and encl = "," ""})
    Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.Zip.M.t\<close>
where sep = "and"\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun next{i} x = Next{i} x
fun dest_next{i} (Next{i} x) = x\<close>\<close>

structure Base =
struct
\<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{T_args} inst{i} = 'a{i}\<close>\<close>
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} =
Node\<^eval>\<open>T_Args.Poly_nargs' ()\<close>_Node\<^eval>\<open>string_of_int (T_Args.Poly_nargs () + 1)\<close>(
  open Base
  type @{T_args} inst\<^eval>\<open>string_of_int (T_Args.Poly_nargs () + 1)\<close> = @{T_args} next{i}
  structure N = N{i}
)\<close>\<close>

structure Base =
struct
\<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{T_args} inst{i} = 'a{i}\<close> where start = 2\<close>
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Zipper"\<close>(
  open Base
  type @{T_args} inst1 = @{T_args} N{i}.node
  structure Z = Z{i}
)\<close>\<close>

structure Base =
struct
  structure A = A
  fun ncontent x = x |> A.id ()
  fun dest_ncontent x = x |> A.id ()
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure N{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Node" ^ "_Content_Next"\<close>(
  open Base
  structure N = N{i}
  type @{T_args} ncontent = @{T_args} ncontent{i}
  type @{T_args} nnext = (@{ParaT_args},
    @{T_args} Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.Zip.M.t
  fun nnext x = x |> A.arr dest_next{i}
  fun dest_nnext x = x |> A.arr next{i}
)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{T_args} node{i} = @{T_args} N{i}.node\<close>\<close>

end