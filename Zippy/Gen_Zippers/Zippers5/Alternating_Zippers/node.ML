(*  Title:      Zippy/node.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "NODE"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type @{AllT_args} content
  type @{AllT_args} next
  type @{AllT_args} node

  val node : (@{ParaT_args} @{AllT_args} content * @{AllT_args} next, @{AllT_args} node) L.C.cat

  val content : unit -> (@{ParaT_args} @{AllT_args} node, @{AllT_args} content) L.slens
  val next : unit -> (@{ParaT_args} @{AllT_args} node, @{AllT_args} next) L.slens
  val get_content : (@{ParaT_args} @{AllT_args} node, @{AllT_args} content) L.getter
  val get_next : (@{ParaT_args} @{AllT_args} node, @{AllT_args} next) L.getter
  val map_content : (@{ParaT_args} @{AllT_args} node, @{AllT_args} content) L.smodifier
  val map_next : (@{ParaT_args} @{AllT_args} node, @{AllT_args} next) L.smodifier
end

functor \<^eval>\<open>sfx_T_nargs "Node"\<close>(
    type @{AllT_args} content
    type @{AllT_args} next
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat =
      (@{ParaT_args} 'a, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} next = @{AllT_args} next
datatype @{AllT_args} node = Node of
  {content : @{AllT_args} content, next : @{AllT_args} next}

fun node (content, next) = Node {content = content, next = next}

fun get_content (Node {content,...}) = content
fun get_next (Node {next,...}) = next

fun map_content (f, Node {content, next}) = Node {content = f content, next = next}
fun map_next (f, Node {content, next}) = Node {content = content, next = f next}

fun content _ = L.lens get_content map_content
fun next _ = L.lens get_next map_next

end

signature \<^eval>\<open>sfx_T_nargs "LIFT_NODE"\<close> =
sig
  structure N : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  include \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  where type @{AllT_args} content = @{AllT_args} N.content
  where type @{AllT_args} next = @{AllT_args} N.next
  where type @{AllT_args} node = @{AllT_args} N.node
end

functor \<^eval>\<open>sfx_T_nargs "Lift_Node"\<close>(
    structure AF : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
    structure N : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    sharing type N.L.C.cat = AF.cat
    structure AT : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_BASE"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) AT.cat
    val lift : (@{ParaT_args} 'a, 'b) AF.cat -> (@{ParaT_args} 'a, 'b) AT.cat
  ) : \<^eval>\<open>sfx_T_nargs "LIFT_NODE"\<close> =
struct

structure N = N
structure L = L

type @{AllT_args} content = @{AllT_args} N.content
type @{AllT_args} next = @{AllT_args} N.next
type @{AllT_args} node = @{AllT_args} N.node

fun node x = x |> lift N.node
fun node_lens _ = L.lens_get_mk (lift (AF.&&& (N.get_content, N.get_next))) node
fun content _ = L.lens_fst (node_lens ())
fun next _ = L.lens_snd (node_lens ())
fun get_content x = x |> L.get (content ())
fun map_content x = x |> L.modify (content ())
fun get_next x = x |> L.get (next ())
fun map_next x = x |> L.modify (next ())

end
