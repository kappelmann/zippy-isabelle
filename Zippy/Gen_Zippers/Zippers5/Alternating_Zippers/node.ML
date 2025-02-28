(*  Title:      HOCLP/node.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close> =
sig
  structure L : LENS
  type @{T_args} content
  type @{T_args} next
  type @{T_args} node

  val node : (@{ParaT_args}, @{T_args} content * @{T_args} next, @{T_args} node) L.C.cat

  val content : unit -> (@{ParaT_args}, @{T_args} node, @{T_args} content) L.slens
  val next : unit -> (@{ParaT_args}, @{T_args} node, @{T_args} next) L.slens
  val get_content : (@{ParaT_args}, @{T_args} node, @{T_args} content) L.getter
  val get_next : (@{ParaT_args}, @{T_args} node, @{T_args} next) L.getter
  val map_content : (@{ParaT_args}, @{T_args} node, @{T_args} content) L.smodifier
  val map_next : (@{ParaT_args}, @{T_args} node, @{T_args} next) L.smodifier
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Node"\<close>(
    type @{T_args} content
    type @{T_args} next
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) SLens.C.cat =
struct

structure L = SLens

type @{T_args} content = @{T_args} content
type @{T_args} next = @{T_args} next
datatype @{T_args} node = Node of
  {content : @{T_args} content, next : @{T_args} next}

fun node (content, next) = Node {content = content, next = next}

fun get_content (Node {content,...}) = content
fun get_next (Node {next,...}) = next

fun map_content (f, Node {content, next}) = Node {content = f content, next = next}
fun map_next (f, Node {content, next}) = Node {content = content, next = f next}

fun content _ = L.lens get_content map_content
fun next _ = L.lens get_next map_next

end

signature \<^eval>\<open>T_Args.suffix_Poly_nargs "LIFT_NODE"\<close> =
sig
  structure N : \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
  where type @{T_args} content = @{T_args} N.content
  where type @{T_args} next = @{T_args} N.next
  where type @{T_args} node = @{T_args} N.node
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Lift_Node"\<close>(
    structure AF : ARROW
    structure N : \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
    sharing type N.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AT.cat
    val lift : ('p1, 'a, 'b) AF.cat -> ('p1, 'a, 'b) AT.cat
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIFT_NODE"\<close> =
struct

structure N = N
structure L = L

type @{T_args} content = @{T_args} N.content
type @{T_args} next = @{T_args} N.next
type @{T_args} node = @{T_args} N.node

fun node x = x |> lift N.node
fun node_lens _ = L.lens_get_mk (lift (AF.&&& (N.get_content, N.get_next))) node
fun content _ = L.lens_fst (node_lens ())
fun next _ = L.lens_snd (node_lens ())
fun get_content x = x |> L.get (content ())
fun map_content x = x |> L.modify (content ())
fun get_next x = x |> L.get (next ())
fun map_next x = x |> L.modify (next ())

end
