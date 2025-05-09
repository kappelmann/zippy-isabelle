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

  (* constructors *)
  val container_no_parent : @{ParaT_args encl = "(" ")"} AE.exn -> 'c -> 'c * (@{ParaT_args} 'p) M.t
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val node_no_next{i} : @{ParaT_args encl = "(" ")"} AE.exn -> @{AllT_args} ZCore.N{i}.content ->
    @{AllT_args} ZCore.N{i}.node\<close>\<close>

  (* lenses *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Node{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Node{i}.container = Z{i}.zipper
  sharing type Node{i}.data = ZCore.N{i}.node

  structure Node_Co{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  sharing type Node_Co{i}.container = Z{i}.zipper
  sharing type Node_Co{i}.data = ZCore.N{i}.content

  structure Node_Next{i} : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} ZCore.N{i}.next
  sharing type Node_Next{i}.container = Z{i}.zipper\<close>\<close>

  val set_no_next : @{ParaT_args encl = "(" ")"} AE.exn ->
    (@{ParaT_args} 's, (@{ParaT_args} 'i) M.t) L.smodifier -> 's -> 's
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

(* constructors *)
fun container_no_parent e c = (c, no_parent e)
\<^imap>\<open>\<open>{i}\<close> => \<open>
fun node_no_next{i} e c = ZCore.N{i}.node (c, no_next e)\<close>\<close>

(* lenses *)
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Node{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Z{i}.ZD.Co
  structure L2 = ZCore_Co{i})

structure Node_Co{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Node{i}
  structure L2 = ZCore.N{i}.Co)

structure Node_Next{i} = \<^eval>\<open>sfx_T_nargs "Comp_Structured_Lens"\<close>(
  structure L1 = Node{i}
  structure L2 = ZCore.N{i}.Next)\<close>\<close>

fun set_no_next exn nextl z = L.set_modify nextl (no_next exn, z)

end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor Instantiate_Zippy_Node_{j}(
    type @{AllT_args} inst
    structure Z : ZIPPY_NODE
  ) :
    ZIPPY_NODE
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

