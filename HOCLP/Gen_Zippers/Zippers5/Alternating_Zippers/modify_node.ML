(*  Title:      HOCLP/modify_node.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Node"\<close>(
    structure N : \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
    where type @{T_args} content = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.content
    where type @{T_args} next = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.next
    where type @{T_args} node = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) N.node
  = N

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Replace_Node" ^ "_Content_Next"\<close>(
    structure A : KLEISLI_ARROW_BASE
    structure N : \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.cat
    type @{T_args} ncontent
    val ncontent : (@{ParaT_args}, @{T_args} N.content, @{T_args} ncontent) A.cat
    val dest_ncontent : (@{ParaT_args}, @{T_args} ncontent, @{T_args} N.content) A.cat
    type @{T_args} nnext val nnext : (@{ParaT_args}, @{T_args} N.next, @{T_args} nnext) A.cat
    val dest_nnext : (@{ParaT_args}, @{T_args} nnext, @{T_args} N.next) A.cat
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
    where type @{T_args} content = @{T_args} ncontent
    where type @{T_args} next = @{T_args} nnext
    where type @{T_args} node = @{T_args} N.node
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) N.L.C.cat
    where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) N.L.lens
  =
struct

structure L = N.L
type @{T_args} content = @{T_args} ncontent
type @{T_args} next = @{T_args} nnext
type @{T_args} node = @{T_args} N.node

structure SC = Semi_Category(A) open SC A

fun node x = x |> ((dest_ncontent *** dest_nnext) >>> N.node)

fun content _ = L.comp (L.lens_get_mk ncontent dest_ncontent) (N.content ())
fun next _ = L.comp (L.lens_get_mk nnext dest_nnext) (N.next ())

fun get_content x = x |> L.get (content ())
fun get_next x = x |> L.get (next ())
fun map_content x = x |> L.modify (content ())
fun map_next x = x |> L.modify (next ())

end
