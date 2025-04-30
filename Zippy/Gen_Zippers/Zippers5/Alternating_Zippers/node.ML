(*  Title:      Zippy/node.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "NODE"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
  type @{AllT_args} node
  type @{AllT_args} content
  type @{AllT_args} next

  val node :
    (@{ParaT_args} @{AllT_args} content * @{AllT_args} next, @{AllT_args} node) L.C.cat

  structure CO : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} node
  where type @{AllT_args} data = @{AllT_args} content
  sharing type CO.lens = L.lens
  sharing type CO.K.M.t = L.K.M.t

  structure NEXT : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} node
  where type @{AllT_args} data = @{AllT_args} next
  sharing type NEXT.lens = L.lens
  sharing type NEXT.K.M.t = L.K.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Node"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
    type @{AllT_args} content
    type @{AllT_args} next
  ) : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  =
struct

structure L = L

type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} next = @{AllT_args} next
datatype @{AllT_args} node = Node of {content : @{AllT_args} content, next : @{AllT_args} next}

local open L.K.M
in

fun node (content, next) = pure (Node {content = content, next = next})

structure Base = struct open L; type @{AllT_args} container = @{AllT_args} node end
structure CO =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} content
  fun getter (Node {content,...}) = pure content
  fun modifier (f, Node {content, next}) = bind (f content)
    (fn content => node (content, next))
  fun lens _ = L.mk_lens getter modifier
end

structure NEXT =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} next
  fun getter (Node {next,...}) = pure next
  fun modifier (f, Node {content, next}) = bind (f next)
    (fn next => node (content, next))
  fun lens _ = L.mk_lens getter modifier
end
end

end

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>sfx_inst_T_nargs "Instantiate_Node" {i}\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type @{AllT_args} content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.content
    where type @{AllT_args} next = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.next
    where type @{AllT_args} node = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.node
  = Z\<close>\<close>

