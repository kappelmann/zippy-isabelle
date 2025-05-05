(*  Title:      Zippy/zippy_node.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_NODE =
sig
  include ZIPPY_NODE_BASE
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
  sharing type AE.K.M.t = M.t

  (* misc *)
  val no_parent : (@{ParaT_args} @{ParaT_args encl = "(" ")"} AE.exn, 'p) cat
  val no_next : (@{ParaT_args} @{ParaT_args encl = "(" ")"} AE.exn, 'n) cat

  (* lenses *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure NODE{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type NODE{i}.container = Z{i}.zipper
  sharing type NODE{i}.data = ZCORE.N{i}.node
  sharing type NODE{i}.K.M.t = M.t
  sharing type NODE{i}.lens = L.lens

  structure NODE_CO{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type NODE_CO{i}.container = Z{i}.zipper
  sharing type NODE_CO{i}.data = ZCORE.N{i}.content
  sharing type NODE_CO{i}.K.M.t = M.t
  sharing type NODE_CO{i}.lens = L.lens

  structure NODE_NEXT{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZCORE.N{i}.next
  sharing type NODE_NEXT{i}.container = Z{i}.zipper
  sharing type NODE_NEXT{i}.K.M.t = M.t
  sharing type NODE_NEXT{i}.lens = L.lens\<close>\<close>

  val set_no_next : @{ParaT_args encl = "(" ")"} AE.exn ->
    (@{ParaT_args} 's, (@{ParaT_args} 'i) M.t) L.smodifier -> (@{ParaT_args} 's) hom_move
end

functor Zippy_Node(
    structure Z : ZIPPY_NODE_BASE
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
    sharing type AE.K.M.t = Z.M.t
  ) : ZIPPY_NODE =
struct

open Z
structure AE = AE

(* misc *)
val no_parent = AE.throw
val no_next = AE.throw

(* lenses *)
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure NODE{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.CO
  structure L2 = ZCORE_CO{i})

structure NODE_CO{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = NODE{i}
  structure L2 = ZCORE.N{i}.CO)

structure NODE_NEXT{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = NODE{i}
  structure L2 = ZCORE.N{i}.NEXT)\<close>\<close>

fun set_no_next exn nextl z = L.set_modify nextl (no_next exn, z)

end
